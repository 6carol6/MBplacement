//
//  simMaas.cpp
//  implementation of Hadrian NSDI 2013
//  Created by wang xiaoliang on 4/2/14.
//  Copyright (c) 2014 wang xiaoliang. All rights reserved.
//

#include <iostream>
#include <fstream>
#include <Math.h>
#include <lemon/dijkstra.h>
#include <lemon/path.h>
#include <lemon/edmonds_karp.h>

#include "simMaas.h"
#include "util.h"
#include<ctime>

using namespace std;
using namespace lemon;

bool with_pmcap = false;

Digraph        g;
IntNodeMap     PM_CAP(g);
IntNodeMap     node_type(g);
IntArcMap      arc_type(g);
IntNodeMap     subtree_vmcap(g);
DoubleArcMap      arc_upload_cap(g);
DoubleArcMap      arc_download_cap(g);
ParentNodeMap  parent_node(g);

IntArcMap      hosts_allowed(g);

Node           spine;
map<Node,int>     slots;   // including all pm nodes
Tenant_Request_Queue tenant_request_queue;
bool first_built_maxflow;
Digraph flow_net;
map< int, vector<int> > tenant_point_search;

int total=0;
// topology
int oversubscription_spine = 0;
int oversubscription_leaf  = 0;
int oversubscription_tor   = 0;
int oversubscription_pm    = 0;
int caplink_spine2leaf     = 0;
int caplink_leaf2tor       = 0;
int caplink_tor2pm         = 0;
int num_tenant_job         = 0;
//int mv_ratio = 0;
bool findsubtree = false;
int totalslots = 0;

LinkNode* PM_LAYER = NULL;
LinkNode* TOR_LAYER = NULL;
LinkNode* LEAF_LAYER = NULL;
int place1_cnt = 0;
int place2_cnt = 0;

double load_rej[5] = {0,0,0,0,0};
double load_all[5] = {0,0,0,0,0};

void addNodeLayer(LinkNode** layer, Node* node, bool is_start){
    is_start = !is_start;
    if(*layer == NULL){
        *layer = new LinkNode();
        (*layer)->node = g.id(*node);
        (*layer)->is_start = is_start;
        (*layer)->next = NULL;
        return;
    }
    LinkNode* tmp = new LinkNode();
    tmp->node = g.id(*node);
    tmp->is_start = is_start;
    tmp->next = *layer;
    *layer = tmp;
    //cout << g.id(*(PM_LAYER->node)) << endl;
}

int readGraph(const char* argv[])
{
    ifstream lgf_file(argv[1]);
    if (!lgf_file) {
        cout<<"Error opening file .lgf\n";
        return 1;
    }
    try{
        digraphReader(g, lgf_file)
        .attribute("OversubscriptionSpine", oversubscription_spine)
        .attribute("OversubscriptionLeaf",  oversubscription_leaf)
        .attribute("OversubscriptionTor",   oversubscription_tor)
        .attribute("OversubscriptionPM",    oversubscription_pm)
        .attribute("LinkCapSpine2Leaf",     caplink_spine2leaf)
        .attribute("LinkCapLeaf2Tor",       caplink_leaf2tor)
        .attribute("LinkCapTor2Pm",         caplink_tor2pm)
        .attribute("TotalTenantJob",        num_tenant_job)
        //.attribute("Middleboxratio", mv_ratio)
        .run();

    } catch(Exception& error){
        cerr <<"Error:" <<error.what() <<endl;
        return -1;
    }

    return 1;
}

void createTreeTopology()
{
    Node core = g.addNode();
    node_type[core] = CORE;
    parent_node[core] = core;
    subtree_vmcap[core] = -1;

    spine = g.addNode();
    node_type[spine] = SPINE;
    parent_node[spine] = core;
    subtree_vmcap[spine] = oversubscription_spine*oversubscription_leaf*oversubscription_tor*oversubscription_pm;
    totalslots = subtree_vmcap[spine];

    Arc core2spine = g.addArc(core, spine);
    arc_upload_cap[core2spine] = 0;
    arc_download_cap[core2spine] = 0;
    //arc_weight[core2spine]=1;
    arc_type[core2spine]=CORESPINE;

    for (int i=0; i<oversubscription_spine; ++i){
        Node leaf = g.addNode();
        node_type[leaf] = LEAF;
        parent_node[leaf] = spine;
        subtree_vmcap[leaf] = oversubscription_leaf*oversubscription_tor*oversubscription_pm;

        Arc spine2leaf = g.addArc(spine, leaf);
        arc_upload_cap[spine2leaf] = caplink_spine2leaf;
        arc_download_cap[spine2leaf] = caplink_spine2leaf;
        /*arc_weight[spine2leaf]=1;*/
        arc_type[spine2leaf]=SPINELEAF;
        hosts_allowed[spine2leaf] = subtree_vmcap[leaf];

        addNodeLayer(&LEAF_LAYER, &leaf, true);


        //cout << "carolzzzzz:" << g.id(*LEAF_LAYER->node) << endl;
        for (int j=0; j<oversubscription_leaf; ++j){
            Node tor =  g.addNode();
            node_type[tor] = TOR;
            parent_node[tor] = leaf;
            subtree_vmcap[tor] = oversubscription_tor*oversubscription_pm;

            Arc leaf2tor = g.addArc(leaf, tor);
            arc_upload_cap[leaf2tor] = caplink_leaf2tor;
            arc_download_cap[leaf2tor] = caplink_leaf2tor;
            /*arc_weight[leaf2tor]=1; */
            arc_type[leaf2tor]=LEAFTOR;
            hosts_allowed[leaf2tor] = subtree_vmcap[tor];

            addNodeLayer(&TOR_LAYER, &tor, oversubscription_tor-j-1);

            for (int k=0; k<oversubscription_tor; ++k){
                Node pm =  g.addNode();
                node_type[pm] = PM;
                parent_node[pm] = tor;
                subtree_vmcap[pm] = oversubscription_pm;
                slots.insert(pair<Node,int>(pm,oversubscription_pm));
                Arc tor2pm = g.addArc(tor, pm);
                arc_upload_cap[tor2pm] = caplink_tor2pm;
                arc_download_cap[tor2pm] = caplink_tor2pm;
                /*arc_weight[tor2pm]=1; */
                arc_type[tor2pm]=TORPM;
                addNodeLayer(&PM_LAYER, &pm, oversubscription_tor-k-1);
            }
        }
    }
    for(ArcIt a(g); a!=INVALID; a++){
        Node tmp = g.target(a);
        if(with_pmcap && node_type[tmp]==PM){
            PM_CAP[tmp] = 10000;
        }
    }
}

void createTenantRequests()
{
    srand((unsigned)time(0));
    int open_tenant_num = 0;
    int dep_to_open_num = 0;
    int other_dep_num = 0;
    int open_tenant_list[12000];
    for (int i = 0; i<num_tenant_job; ++i){
        /***** here each tenant creates only one VN *****/
        Tenant vn;
        // create vn
        vn.tenant_id = i;

        // varying mean bandwidth requirement for the tenant jobs
        //cout << "=============Tenant " << i << "==============="<<endl;
        vn.min_load = uniformIntDist(BIN_MIN, BIN_MAX);
        //vn.min_load = uniformIntDist(1000, 1500);

        //vn.external_load = 0;
        vn.external_load = uniformIntDist(BEX_MIN, BEX_MAX);//(int)vn.min_load/65.0*30.0;//uniformIntDist(50, 100);

        //vn.sum_appvm_req = uniformIntDist(10, 15);
        vn.sum_appvm_req = uniformIntDist(N_MIN, N_MAX);

        vn.mb_type_num = uniformIntDist(MB_TYPE_NUM_MIN, MB_TYPE_NUM_MAX);//How many types of MBs?
        vn.sum_mb_req = 0;
        for(int j = 0; j < vn.mb_type_num; j++){
            int mv_ratio = uniformIntDist(R_MIN, R_MAX);
            vn.mv_ratio[j] = mv_ratio;
            vn.mb_req_num[j] = (vn.sum_appvm_req%vn.mv_ratio[j])?vn.sum_appvm_req/vn.mv_ratio[j]+1:vn.sum_appvm_req/vn.mv_ratio[j];
            vn.sum_mb_req += vn.mb_req_num[j];
            vn.mb_location[j] = new Placement();
            vn.mb_location[j]->next = NULL;
        }
        vn.placement_success = false;
        vn.appvm_location = new Placement();
        vn.appvm_location->next = NULL;

        //add dependency
        int fraction = uniformIntDist(1, 100);
        //if(fraction < 50)

        //new dependeny arrangement
        if(fraction < OPEN_TENANT_PER){ //Open tenant
            vn.dependency.insert(-1);
            open_tenant_list[open_tenant_num++] = i;
        }
        else if(fraction >= OPEN_TENANT_PER && fraction < DEP_OPEN_TENANT_PER){ //Have dependency to open tenant
            if(open_tenant_num){
                dep_to_open_num++;
                int rand = uniformIntDist(0, open_tenant_num-1);
                vn.dependency.insert(open_tenant_list[rand]);
            }
        }else if(fraction >= DEP_OPEN_TENANT_PER && fraction < DEP_TENANT_PER){ //Other dependency
            int dep_num = 1;//uniformIntDist(1, min((i+1)/2,2));
            while(dep_num--){
                int rand = uniformIntDist(0, i);
                if(rand == i) continue;
                for(list<Tenant>::iterator it1 = tenant_request_queue.begin(); it1!=tenant_request_queue.end(); it1++){
                    if((*it1).tenant_id == rand && (*it1).dep_num == 0){
                        other_dep_num++;
                        vn.dependency.insert(rand);
                        (*it1).dependency.insert(vn.tenant_id);
                        (*it1).dep_num++;
                        break;
                    }
                }
                //vn.dependency.insert(rand);
            }
        }
        vn.dep_num = vn.dependency.size();


        tenant_request_queue.push_back(vn);
    }
    //print the dependency
    for(list<Tenant>::iterator it1 = tenant_request_queue.begin(); it1!=tenant_request_queue.end(); it1++){
        cout << "Tenant " << (*it1).tenant_id << ": ";

        for(set<int>::iterator it = (*it1).dependency.begin(); it!=(*it1).dependency.end(); it++){
            cout << *it << ", ";
        }
        cout << endl;
    }
    cout << "open tenant num: " << open_tenant_num << endl;
    cout << "dep to open tenant num:" << dep_to_open_num << endl;
    cout << "other dep num: " << other_dep_num << endl;
}
/*
void printTreeTopology()
{
    cout<<"     SPINE_"<< g.id(spine) << " cap=" <<subtree_vmcap[spine] <<" \n";

    for (OutArcIt ait(g, spine); ait!=INVALID; ++ait){
        Node leaf = g.target(ait);
        if (leaf == parent_node[spine]) {continue;}
        {
            cout<<"       LEAF_"<< g.id(leaf) << " cap=" <<subtree_vmcap[leaf] <<" fromSpineLink = "<< linkCapfromParent(leaf)<<" \n";
        }
        for (OutArcIt bit(g, leaf); bit!=INVALID; ++bit){
            Node tor = g.target(bit);
            if (tor == parent_node[leaf]) {continue;}
            {
                cout<<"        TOR_"<< g.id(tor) << " cap="<<subtree_vmcap[tor] <<" fromLeafLink = "<< linkCapfromParent(tor)<<" \n";
            }
            for (OutArcIt cit(g, tor); cit!=INVALID; ++cit){
                Node pm = g.target(cit);
                if (pm == parent_node[tor]) {continue;}
                {
                    cout<<"          PM_"<< g.id(pm) << " cap="<<subtree_vmcap[pm] << " fromTorLink = "<< linkCapfromParent(pm)<<" \n";
                }
            }
        }
    }
    cout<<endl;
}
*/
void printTenantRequest(const Tenant& vn)
{
    cout<<"-----------------------------------------"<<endl;
    cout<<" Tenant request is listed at follows: "<<endl;

    cout<<"    Tenant_id       = "<<vn.tenant_id<<endl;
    cout<<"    Sum_APPvm_req   = "<<vn.sum_appvm_req<<endl;

    cout<<"    Load_appvm  = "<<vn.min_load<<endl;
    cout<<"    Load_external  = " <<vn.external_load<<endl;
    //cout<<"    Middlebox_vm_ratio = "<<vn.mv_ratio<<endl;
    cout<<"    Middlebox_req      "<<endl;
    for(int i = 0; i < vn.mb_type_num; i++){
        cout << vn.mb_req_num[i] <<"/" << vn.sum_mb_req << endl;
    }
    //cout<<"    Sum_MB_req = "<<vn.sum_mb_req<<endl;
    cout<<"-----------------------------------------"<<endl;
}

void printAllocation(Tenant &t)
{
        Placement *p = t.appvm_location->next;

        cout<<"vm location: ";
        while(p){
            cout<<"<"<<p->pm_id<<","<<p->amount<<">";
            p = p->next;
        }
        cout<<endl;
        cout<<"mb location: ";
        for(int i = 0; i < t.mb_type_num; i++){
            Placement *q = t.mb_location[i]->next;
            while(q){
                cout<<"<"<<q->pm_id<<","<<q->amount<<">";
                q = q->next;
            }
        }
        cout<<endl;
}
bool checkslot(Tenant* t, Node* node){
    //cout << "checkslot" << endl;
    //cout << subtree_vmcap[*node] <<" "<< g.id(*node) <<endl;
    int total = t->sum_appvm_req+t->sum_mb_req;
    if(subtree_vmcap[*node] >= total) return true;
    return false;
}
LinkNode* FindLowestSubtree(Tenant* t, int layer, int again){
    //cout << "findtree" << layer <<endl;
    if(layer == 4) return 0;
    LinkNode* p = NULL;
    if(layer == 0){ p = PM_LAYER;}
    else if(layer == 1){ p = TOR_LAYER;}
    else if(layer == 2){ p = LEAF_LAYER;}
    else{ //layer == 3; SPINE_LAYER
        LinkNode* tmp = new LinkNode();
        tmp->node = 1;
        tmp->next = NULL;
        if(checkslot(t, &g.nodeFromId(1))){
            for(OutArcIt ait(g, g.nodeFromId(1)); ait != INVALID; ait++){
                if(checkslot(t, &g.target(ait))){
                   return FindLowestSubtree(t, layer-1, again);
                }
            }
            return tmp;//return g.nodeFromId(1);
        }
        return FindLowestSubtree(t, layer+1, again);
    }
    //cout << g.id(*(PM_LAYER->node))<< "carolz"<<endl;
    while(p->next){
        if(p->node < again && checkslot(t, &g.nodeFromId(p->node))){
            if(layer != 0){
                for(OutArcIt ait(g, g.nodeFromId(p->node)); ait != INVALID; ait++){
                    if(checkslot(t, &g.target(ait))){
                        return FindLowestSubtree(t, layer-1, again);
                    }
                }
            }
            return p;//return g.nodeFromId(p->node);
        }
        p = p->next;
    }
    if(p->node < again && checkslot(t, &g.nodeFromId(p->node))){
        if(layer != 0){
            for(OutArcIt ait(g, g.nodeFromId(p->node)); ait != INVALID; ait++){
                if(checkslot(t, &g.target(ait))){
                    return FindLowestSubtree(t, layer-1, again);
                }
            }
        }
        return p;//return g.nodeFromId(p->node);
    }
    return FindLowestSubtree(t, layer+1, again);
}

void Clean(Tenant* t, int sum_appvm_req, int sum_mb_req)
{
    t->sum_appvm_req = sum_appvm_req; t->sum_mb_req = sum_mb_req;
    Placement *p = t->appvm_location->next;
    Placement *q;
    while(p){
        q = p->next;
        free(p);
        p = q;
    }
    t->appvm_location->next = NULL;

    for(int i = 0; i < t->mb_type_num; i++){
        p = t->mb_location[i]->next;
        while(p){
            q = p->next;
            free(p);
            p = q;
        }
        t->mb_location[i]->next = NULL;
    }
    t->placement_success = false;
}

double s_util()
{
    return (double)subtree_vmcap[spine]/totalslots;
}

void AddPlacement(Placement* head, int num, int pm_id, double percentage){
    if(num == 0) return;
    Placement* p = head;
    while(p->next){
        if(p->pm_id == pm_id){
            p->amount += num;
            return;
        }
        p = p->next;
    }
    if(p->pm_id == pm_id){ p->amount += num;return;}
    Placement* tmp = new Placement();
    tmp->pm_id = pm_id; tmp->amount = num; tmp->percentage = percentage;
    tmp->next = head->next;
    head->next = tmp;
}

void Alloc(Tenant* t, int appvm_n, int mb_n, Node root, IntNodeMap* subtree_vmcap_active){
    if(node_type[root] == PM){
        //cout <<t->sum_appvm_req<< " " << t->sum_mb_req<< endl;
        //cout << appvm_n << " " << mb_n <<endl;
        AddPlacement(t->appvm_location, appvm_n, g.id(root), 0);
        //cout << "test" << t->appvm_location->next->pm_id << endl;
        AddPlacement(t->mb_location[0], mb_n, g.id(root), 0);
        t->sum_appvm_req -= appvm_n;
        t->sum_mb_req -= mb_n;
        if(t->sum_appvm_req == 0 && t->sum_mb_req == 0) t->placement_success = true;
        return;
    }
    //if(t->min_load > t->mv_ratio*t->external_load){ //Placement1
        cout << "placement1"<< endl;
        for(OutArcIt ait(g, root); ait != INVALID; ait++){
            Node child = g.target(ait);
            if(appvm_n != 0){
                cout << "appvm_n" << appvm_n << "/"<<subtree_vmcap[child]<< endl;
                //cout << subtree_vmcap[child]<<"place1"<<" "<< t->sum_appvm_req<< endl;
                int n = min(appvm_n, subtree_vmcap[child]);
                if(subtree_vmcap[child] > n){
                    cout << "mb_n: " << mb_n << "/"<<subtree_vmcap[child]<< endl;
                    Alloc(t, n, min(mb_n,subtree_vmcap[child]-n), child, subtree_vmcap_active);
                    //printAllocation(*t);
                    mb_n -= min(mb_n,subtree_vmcap[child]-n);
                    appvm_n -= n;
                }else{
                    Alloc(t, n, 0, child, subtree_vmcap_active);
                    appvm_n -= n;
                }
            }else{
                 //printAllocation(*t);
               // cout << subtree_vmcap[child]<<"place2"<< endl;
               cout << "mb_n: " << mb_n << "/"<<subtree_vmcap[child]<< endl;
                int n = min(mb_n, subtree_vmcap[child]);
                Alloc(t, 0, n, child,subtree_vmcap_active);
                mb_n -= n;
            }
        }
    /*}else{ //Placement2
        cout << "placement2"<< endl;
        while(appvm_n != 0 || mb_n!=0){
            cout << "aaa"<< endl;
            int place_cnt = 0;
            for(OutArcIt ait(g,root); ait != INVALID; ait++){
                Node child = g.target(ait);
                cout << "bbb"<<subtree_vmcap[child]<<" " << (*subtree_vmcap_active)[child]<<endl;

                if(subtree_vmcap[child]==(*subtree_vmcap_active)[child]) continue;
                int mb = min(1, mb_n);
                int app = min(t->mv_ratio*mb, appvm_n);
                if(mb_n == 0) app = appvm_n;
                if(appvm_n == 0 && mb_n==0) break;
                if(app == 0 && mb == 0) break;
                if(place_cnt == 2) break;
                place_cnt++;

                if(mb + app > subtree_vmcap[child]-(*subtree_vmcap_active)[child]){
                    if(subtree_vmcap[child]-(*subtree_vmcap_active)[child] > app/2){
                        app = min(subtree_vmcap[child]-(*subtree_vmcap_active)[child]-mb, app);
                    }else{
                        mb = 0;
                        app = min(app,subtree_vmcap[child]-(*subtree_vmcap_active)[child]);
                    }
                }
                cout << app << " " << mb << endl;
                (*subtree_vmcap_active)[child] += (app+mb);
                appvm_n -= app; mb_n -= mb;
                Alloc(t, app, mb, child, subtree_vmcap_active);
            }
        }
    }*/
/*
    for(OutArcIt ait(g, root); ait != INVALID; ait++){
        Node child = g.target(ait);
        if(t->min_load > t->mv_ratio*t->external_load){ //Placement1
            //cout << "Placement1:" << endl;
            if(t->sum_appvm_req != 0){
                int n = min(t->sum_appvm_req, subtree_vmcap[child]);
                if(subtree_vmcap[child] > n)
                    Alloc(t, n, subtree_vmcap[child]-n, child, subtree_vmcap_active);
            }else{
                int n = min(t->sum_mb_req, subtree_vmcap[child]);
                Alloc(t, 0, n, child, subtree_vmcap_active);
            }
        }else{//Placement2
            //cout << "Placement2:" << endl;
            if(t->sum_mb_req + t->sum_appvm_req <= subtree_vmcap[child]){
                Alloc(t, t->sum_appvm_req, t->sum_mb_req, child, subtree_vmcap_active);
            }else{
                int n = min(t->sum_mb_req + t->sum_appvm_req, subtree_vmcap[child]);
                if(subtree_vmcap[child]< 0) cout << "aaaa"<< endl;
                int R = t->mv_ratio;
                //int app = min((n*R)/(R+1), t->sum_appvm_req);
                //if(app == 0) cout << "aaaaa"<< endl;
                int mb = min((int)ceil((double)n/(R+1)), t->sum_mb_req);
                int app = min(subtree_vmcap[child]-mb,t->sum_appvm_req);
                Alloc(t, app, mb, child, subtree_vmcap_active);
            }
            if(t->placement_success) return;
        }
    }*/
}

void ModifyCap(DoubleArcMap *up_arc_cap_active, DoubleArcMap* down_arc_cap_active, DoubleNodeMap* pm_cap_active){
    for(ArcIt a(g); a!=INVALID; a++){
        arc_upload_cap[a] -= (*up_arc_cap_active)[a];
        arc_download_cap[a] -= (*down_arc_cap_active)[a];
        Node tmp = g.target(a);
        if(with_pmcap && node_type[tmp]==PM){
            PM_CAP[tmp] -= (*pm_cap_active)[tmp];
            if(PM_CAP[tmp] < 0) cout << "errorPMCAP" << endl;
        }
    }
}
void ModifyHostAllowed(Tenant* t){
    Placement* p = t->appvm_location->next;
    while(p){
        Node tmpa = g.nodeFromId(p->pm_id);
        subtree_vmcap[tmpa] -= p->amount;
        while(g.id(parent_node[tmpa]) != 0){
            tmpa = parent_node[tmpa];
            subtree_vmcap[tmpa] -= p->amount;
        }
        p = p->next;
    }
    for(int i = 0; i < t->mb_type_num; i++){
        p = t->mb_location[i]->next;
        while(p){
            Node tmpa = g.nodeFromId(p->pm_id);
            subtree_vmcap[tmpa] -= p->amount;
            while(g.id(parent_node[tmpa]) != 0){
                tmpa = parent_node[tmpa];
                subtree_vmcap[tmpa] -= p->amount;
            }
            p = p->next;
        }
    }
}
bool ReserveBWof2Nodes_unblanced(int src, int dst, double uplink_bw, double downlink_bw, DoubleArcMap* up_arc_cap_active, DoubleArcMap* down_arc_cap_active){
    //bandwidth constraint, write later
    if(src == dst){

    }

    while(src != dst){
        //add - note edge cap
        Node nodeSRC = g.nodeFromId(src);
        Node nodeDST = g.nodeFromId(dst);
        for(OutArcIt ait(g, parent_node[nodeSRC]); ait != INVALID; ait++){
            //cout << "bw_test" << (*up_arc_cap_active)[ait] << " " << uplink_bw << endl;
            Node tmp = g.target(ait);
            if(tmp == nodeSRC){
                (*up_arc_cap_active)[ait] += uplink_bw;
                cout << "compareUP" << arc_upload_cap[ait] << " " << (*up_arc_cap_active)[ait] << endl;
                if(arc_upload_cap[ait] < (*up_arc_cap_active)[ait]) return false;
            }
        }
        for(OutArcIt ait(g, parent_node[nodeDST]); ait != INVALID; ait++){
            Node tmp = g.target(ait);
            if(tmp == nodeDST){
                (*down_arc_cap_active)[ait] += downlink_bw;
                cout << "compareDOWN" << arc_download_cap[ait] << " " << (*down_arc_cap_active)[ait] << endl;
                if(arc_download_cap[ait] < (*down_arc_cap_active)[ait]) return false;
            }
        }
        src = g.id(parent_node[nodeSRC]);
        dst = g.id(parent_node[nodeDST]);
    }
    return true;
}

bool ReserveBWof2Nodes(int a, int b, double uplink_bw, double downlink_bw, DoubleArcMap *up_arc_cap_active, DoubleArcMap *down_arc_cap_active){
    while(a != b){
        //add - note edge cap
        Node nodeA = g.nodeFromId(a);
        Node nodeB = g.nodeFromId(b);
        for(OutArcIt ait(g, parent_node[nodeA]); ait != INVALID; ait++){
            Node tmp = g.target(ait);
            if(tmp == nodeA){
                (*up_arc_cap_active)[ait] += uplink_bw;
                (*down_arc_cap_active)[ait] += downlink_bw;
                cout << "compareA" << arc_upload_cap[ait] << " " << (*up_arc_cap_active)[ait] << endl;
                cout << "compareA" << arc_download_cap[ait] << " " << (*down_arc_cap_active)[ait] << endl;
                if(arc_upload_cap[ait] < (*up_arc_cap_active)[ait]) return false;
                if(arc_download_cap[ait] < (*down_arc_cap_active)[ait]) return false;
            }
        }
        for(OutArcIt ait(g, parent_node[nodeB]); ait != INVALID; ait++){
            Node tmp = g.target(ait);
            if(tmp == nodeB){
                (*up_arc_cap_active)[ait] += uplink_bw;
                (*down_arc_cap_active)[ait] += downlink_bw;
                cout << "compareB" << arc_upload_cap[ait] << " " << (*up_arc_cap_active)[ait] << endl;
                cout << "compareB" << arc_download_cap[ait] << " " << (*down_arc_cap_active)[ait] << endl;
                if(arc_upload_cap[ait] < (*up_arc_cap_active)[ait]) return false;
                if(arc_download_cap[ait] < (*down_arc_cap_active)[ait]) return false;
            }
        }
        a = g.id(parent_node[nodeA]);
        b = g.id(parent_node[nodeB]);
    }
    return true;
}
/*
void ReArrangePlacement(Tenant* t){
    int pm_app = 0; int pm_mb = 0;
    Placement* p = t->mb_location->next;
    Placement* first = NULL;
    while(p){
        pm_mb++;
        p = p->next;
    }
    p = t->appvm_location;
    while(p->next){
        pm_app++;
        if(p->pm_id == t->mb_location->next->pm_id) first = p;
        p = p->next;
    }

    int mod = pm_app/pm_mb;
    if(!first) return;
    if(mod<2){
        return;
    }
    p = t->mb_location->next;

    //int cnt = 0;
    Placement* q = t->appvm_location->next;
    for(int cnt = 0; cnt < pm_app; cnt++){
        if(cnt%mod == 0){
            if(p->pm_id == first->pm_id){
                if(!(subtree_vmcap[g.nodeFromId(q->pm_id)] + q->amount < p->amount+first->amount) || !(subtree_vmcap[g.nodeFromId(p->pm_id)]+p->amount+subtree_vmcap[g.nodeFromId(first->pm_id)]+first->amount < q->amount)) continue;
                int amount_tmp = first->amount;
                p->pm_id = q->pm_id;
                first->amount = q->amount;
                q->amount = amount_tmp;
                first = first->next;
                p = p->next;
                if(!first || !p) break;
            }else{
                cout << "something error?" << endl;
            }
        }
        q = q->next;
    }
}
*/
bool ReserveUpLink(int node_id, double upload_bw, double download_bw, DoubleArcMap* up_arc_cap_active, DoubleArcMap* down_arc_cap_active){
    if(upload_bw < DOUBLE_ZERO && download_bw < DOUBLE_ZERO) return true;
    Node nodeA = g.nodeFromId(node_id);
    for(OutArcIt ait(g, parent_node[nodeA]); ait != INVALID; ait++){
        Node tmp = g.target(ait);
        if(tmp == nodeA){
            (*up_arc_cap_active)[ait] += upload_bw;
            (*down_arc_cap_active)[ait] += download_bw;
            if(arc_upload_cap[ait] < (*up_arc_cap_active)[ait]) return false;
            if(arc_download_cap[ait] < (*down_arc_cap_active)[ait]) return false;
            break;
        }
    }
    return true;
}

bool ReserveBin(Tenant* t, DoubleArcMap* up_arc_cap_active, DoubleArcMap* down_arc_cap_active, DoubleNodeMap* pm_cap_active){
   Placement *p = t->appvm_location->next;
    set<int> s;
    while(p){
        double bw = min((t->sum_appvm_req-p->amount)*t->min_load, p->amount*t->min_load);
        if(!ReserveUpLink(p->pm_id, bw, bw, up_arc_cap_active, down_arc_cap_active)) return false;
        s.insert(p->pm_id);
        Node node = g.nodeFromId(p->pm_id);
        (*pm_cap_active)[node] += (p->amount/2)*t->min_load;
        cout << (*pm_cap_active)[node] << "/" << PM_CAP[node] << endl;
        if(with_pmcap && (*pm_cap_active)[node] > PM_CAP[node]) return false;
        p = p->next;
    }
    while(s.size()!=1){
        set<int> s_tmp;
        set<int>::reverse_iterator rit;
        for(rit=s.rbegin();rit!=s.rend();rit++){
            s_tmp.insert(g.id(parent_node[g.nodeFromId(*rit)]));
        }
        for(rit=s_tmp.rbegin();rit!=s_tmp.rend();rit++){
            double bw;
            for(OutArcIt ait(g, g.nodeFromId(*rit)); ait != INVALID; ait++){
                bw += (*up_arc_cap_active)[ait];
            }
            bw = min(bw, t->sum_appvm_req*t->min_load-bw);
            if(!ReserveUpLink((*rit), bw, bw, up_arc_cap_active, down_arc_cap_active)) return false;
        }
        s = s_tmp;
    }
    return true;
}

bool ReserveBWof2MBs(Placement* src, Placement* dst, double bw, DoubleArcMap* up_arc_cap_active, DoubleArcMap* down_arc_cap_active, DoubleNodeMap* pm_cap_active){
    Placement* p = src;
    Placement* q = dst;
    double pper = p->percentage;
    double qper = q->percentage;
   // double sum_p =0 ;
    //double sum_q = 0;
    while(p){

        pper = p->percentage;
        //if(q == NULL && p != NULL) cout <<"BUG" << endl;

        while(q!= NULL && pper > qper){
            cout << "p/q:" << pper << "/" << qper<<endl;
            double bw_tmp = bw*qper;
            if(!ReserveBWof2Nodes_unblanced(p->pm_id, q->pm_id, bw_tmp, bw_tmp, up_arc_cap_active, down_arc_cap_active)){
                return false;
            }
            pper -= qper;
            q = q->next;
            if(q != NULL) qper = q->percentage;
        }
        //cout << "-------1------"<<endl;
        //if(q == NULL && pper > DOUBLE_ZERO) cout <<"qNULL"<< pper << endl;
        if(pper > DOUBLE_ZERO){
            cout << "p/q:" << pper << "/" << qper <<endl;
            double bw_tmp = bw*pper;
            if(!ReserveBWof2Nodes_unblanced(p->pm_id, q->pm_id, bw_tmp, bw_tmp, up_arc_cap_active, down_arc_cap_active)){
                return false;
            }
            qper -= pper;
            pper -= pper;

            if(qper < DOUBLE_ZERO){
                q = q->next;
                if(q != NULL) qper = q->percentage;
            }
        }
        //if(pper > DOUBLE_ZERO) cout <<"dayu"<<pper<< endl;
//cout << "-------2------"<<endl;
        p = p->next;
    }
    //if(sum_p != 1) cout << "errorp" << sum_p << endl;
    //if(sum_q != 1) cout << "errorq" << sum_q <<endl;
   // cout << "============"<<endl;
    return true;
}

bool ReserveBWof2Tenant(Tenant* src, Tenant* dst, double bw_sum, DoubleArcMap* up_arc_cap_active, DoubleArcMap* down_arc_cap_active, DoubleNodeMap* pm_cap_active){
    Placement* p = src->appvm_location->next;

    while(p){
        double bw = bw_sum*p->percentage;

        //src->mb
        Placement* q = dst->mb_location[0]->next;
        while(q){
            cout << "bw_test" << p->percentage << " " <<q->percentage<<endl;
            if(!ReserveBWof2Nodes_unblanced(p->pm_id, q->pm_id, bw*q->percentage, bw*q->percentage, up_arc_cap_active, down_arc_cap_active)) return false;
            q = q->next;
        }
        //mb
        for(int i = 1; i < dst->mb_type_num; i++){
            cout <<"mb"<<i-1<<" -> "<<"mb" << i << endl;
            ReserveBWof2MBs(dst->mb_location[i-1]->next, dst->mb_location[i]->next, bw, up_arc_cap_active, down_arc_cap_active, pm_cap_active);
        }
        //mb->dst
        cout <<"mb"<<dst->mb_type_num-1<<" -> dst"<<endl;
        ReserveBWof2MBs(dst->mb_location[dst->mb_type_num-1]->next, dst->appvm_location->next, bw, up_arc_cap_active, down_arc_cap_active, pm_cap_active);

        p = p->next;
    }
    return true;
}


bool ReserveBex(Tenant* t, DoubleArcMap* up_arc_cap_active, DoubleArcMap* down_arc_cap_active, DoubleNodeMap* pm_cap_active){
   for(auto it = tenant_request_queue.begin(); it != tenant_request_queue.end(); it++){
        //if find a dependency - can be optimized
        if(t->dependency.find((*it).tenant_id) != t->dependency.end() && ((*it).dependency.find(-1) != (*it).dependency.end() || (*it).dependency.find(t->tenant_id) != (*it).dependency.end())){
            if(!(*it).placement_success) continue;
            if(t->tenant_id == (*it).tenant_id) break;

            cout << "Dependency: " << (*it).tenant_id << "<-" << t->tenant_id << endl;
            double bw_sum = min(t->sum_appvm_req*t->external_load, (*it).sum_appvm_req*(*it).external_load);
            //may cause something wrong with &(*it)
            if(!ReserveBWof2Tenant(t, &(*it), bw_sum, up_arc_cap_active, down_arc_cap_active, pm_cap_active)) return false;
            cout << "Dependency: " << (*it).tenant_id << "->" << t->tenant_id << endl;
            if(!ReserveBWof2Tenant(&(*it), t, bw_sum, up_arc_cap_active, down_arc_cap_active, pm_cap_active)) return false;
        }
   }
    return true;
}

bool ReserveBW_try(Tenant* t, DoubleArcMap* up_arc_cap_active, DoubleArcMap* down_arc_cap_active, DoubleNodeMap* pm_cap_active){

    if(!ReserveBin(t, up_arc_cap_active, down_arc_cap_active, pm_cap_active)) return false;
    //Open Tenant
    if(t->dependency.find(-1) != t->dependency.end()) return true;
    //Client Tenant
    if(!ReserveBex(t, up_arc_cap_active, down_arc_cap_active, pm_cap_active)) return false;
    return true;
}

void Invert(Placement *head){
    Placement* p = head->next;
    Placement* q = p->next;
    p->next = NULL;
    while(q != NULL){
        Placement* r = q->next;
        q->next = p;
        p = q;
        q = r;
    }
    head->next = p;
}

void UnpackMBs(Placement* mb_location[], int mb_type_num, int mb_req_num[]){
    int mb_req_num_tmp[10];
    memcpy(&mb_req_num_tmp, mb_req_num, sizeof(mb_req_num_tmp));
    Placement* head = mb_location[0]->next;
    mb_location[0]->next = NULL;
    for(int i = 0; i < mb_type_num; i++){
        double sum = 0;
        while(head != NULL && head->amount <= mb_req_num_tmp[i]){
            AddPlacement(mb_location[i], head->amount, head->pm_id, (double)head->amount/mb_req_num[i]);
            sum += (double)head->amount/mb_req_num[i];
            mb_req_num_tmp[i] -= head->amount;
            Placement* cleantmp = head;
            head = head->next;
            delete(cleantmp);
        }
        if(mb_req_num_tmp[i] != 0){
            AddPlacement(mb_location[i], mb_req_num_tmp[i], head->pm_id, (double)mb_req_num_tmp[i]/mb_req_num[i]);
            sum += (double)mb_req_num_tmp[i]/mb_req_num[i];
            head->amount -= mb_req_num_tmp[i];
        }
        if(sum != 1.0) cout << "error: " << sum << endl;
    }
}

void DivideAPPs(Placement* head, int sum){
    Placement* p = head->next;
    while(p){
        p->percentage = (double)p->amount/sum;
        p = p->next;
    }
}

bool placement(Tenant* t){
    int level = 0;
    int again = 999999;
    LinkNode* ln = FindLowestSubtree(t, level, again);
    int cnt = 1;

    while(ln != NULL && ln->node!=0){//while(node_type[st] != CORE){
        //if(ln->is_last) is_place1 = true;
        //cout << "carolz"<<ln->node << endl;
        Node st = g.nodeFromId(ln->node);
        int sum_appvm_req = t->sum_appvm_req;
        int sum_mb_req = t->sum_mb_req;
        IntNodeMap subtree_vmcap_active(g,0);
        Alloc(t, t->sum_appvm_req, t->sum_mb_req, st, &subtree_vmcap_active);
        t->sum_appvm_req = sum_appvm_req;
        t->sum_mb_req = sum_mb_req;
        DivideAPPs(t->appvm_location, t->sum_appvm_req);
        UnpackMBs(t->mb_location, t->mb_type_num, t->mb_req_num);

        for(int i = 0; i < t->mb_type_num; i++){
            if(i%2 == t->mb_type_num%2){
                Invert(t->mb_location[i]);
            }
        }
        printAllocation(*t);//test
        if(t->placement_success){
            DoubleArcMap up_arc_cap_active(g, 0.0);
            DoubleArcMap down_arc_cap_active(g, 0.0);
            DoubleNodeMap pm_cap_active(g,0.0);
            if(ReserveBW_try(t, &up_arc_cap_active, &down_arc_cap_active, &pm_cap_active)){
                cout<<"Tenant accepted!"<<endl;
                ModifyCap(&up_arc_cap_active, &down_arc_cap_active, &pm_cap_active);
                ModifyHostAllowed(t);
                return true;
            }else{
                cout << "Not enough Bandwidth" << endl;
                Clean(t, sum_appvm_req, sum_mb_req);
            }

        }else{
            cout << "Not enough Slot" << endl;
            Clean(t, sum_appvm_req, sum_mb_req);
        }
        //cout << "carolz" << g.id(st) << endl;
        //level++;
        //st = FindLowestSubtree(t, level);
        ln = ln->next;
        while(ln!=NULL && subtree_vmcap[g.nodeFromId(ln->node)]<t->sum_appvm_req+t->sum_mb_req){
            ln = ln->next;
        }
        if(ln == NULL) break;
        if(ln->is_start){
            if(node_type[g.nodeFromId(ln->node)] == PM) again = 1;
            else if(node_type[g.nodeFromId(ln->node)] == TOR) again = 49;
            ln = FindLowestSubtree(t, level+1, ln->node+again);
        }
        cnt++;
        if(cnt > 40) break;
    }/*
                    if(1.0-s_util() >= 0.5 && 1.0-s_util() < 0.55){
                     if(t->sum_appvm_req < 7){
                        load_rej[0]++;
                    }else if(t->sum_appvm_req < 9){
                        load_rej[1]++;
                    }else if(t->sum_appvm_req < 11){
                        load_rej[2]++;
                    }else if(t->sum_appvm_req < 13){
                        load_rej[3]++;
                    }else{
                        load_rej[4]++;
                    }
                }*/
    cout << "Reject!" << endl;
    return false;
}

//main process
void place(){

    int total_req = 0;
    int accept_req = 0;
    int all_place1_cnt = 0;
    int all_place2_cnt = 0;
    for (auto it = tenant_request_queue.begin(); it != tenant_request_queue.end(); ++it)
    {
        Tenant t = (*it);
        cout<<"\ncurrent tenant: "<<t.tenant_id<<endl;
        printTenantRequest(t);

        if(placement(&t)){
            printAllocation(t);
            tenant_request_queue.emplace(it, t);
            accept_req++;
        }
/*
        if(total_req == 200){
            ofstream slot_out("./test17/pmslot200.txt", ios::app);
            ofstream bw_out("./test17/pmbw200.txt", ios::app);
            LinkNode* p = PM_LAYER;
            while(p != NULL){
                slot_out<<subtree_vmcap[g.nodeFromId(p->node)]<< endl;
                double bw_up = 0; double bw_down = 0;
                for(OutArcIt ait(g, parent_node[g.nodeFromId(p->node)]); ait != INVALID; ait++){
                    if(g.id(g.target(ait)) == p->node){
                        bw_up = arc_upload_cap[ait];
                        bw_down = arc_download_cap[ait];
                        break;
                    }
                }
                bw_out << bw_up << endl;
                bw_out << bw_down << endl;
                p = p->next;
            }

        }
        if(total_req == 2000){
            ofstream slot_out("./test17/pmslot2000.txt", ios::app);
            ofstream bw_out("./test17/pmbw2000.txt", ios::app);
            LinkNode* p = PM_LAYER;
            while(p != NULL){
                slot_out<<subtree_vmcap[g.nodeFromId(p->node)]<< endl;
                double bw_up = 0; double bw_down = 0;
                for(OutArcIt ait(g, parent_node[g.nodeFromId(p->node)]); ait != INVALID; ait++){
                    if(g.id(g.target(ait)) == p->node){
                        bw_up = arc_upload_cap[ait];
                        bw_down = arc_download_cap[ait];
                        break;
                    }
                }
                bw_out << bw_up << endl;
                bw_out << bw_down << endl;
                p = p->next;
            }

        }
        if(total_req == 6000){
            ofstream slot_out("./test17/pmslot6000.txt", ios::app);
            ofstream bw_out("./test17/pmbw6000.txt", ios::app);
            LinkNode* p = PM_LAYER;
            while(p != NULL){
                slot_out<<subtree_vmcap[g.nodeFromId(p->node)]<< endl;
                double bw_up = 0; double bw_down = 0;
                for(OutArcIt ait(g, parent_node[g.nodeFromId(p->node)]); ait != INVALID; ait++){
                    if(g.id(g.target(ait)) == p->node){
                        bw_up = arc_upload_cap[ait];
                        bw_down = arc_download_cap[ait];
                        break;
                    }
                }
                bw_out << bw_up << endl;
                bw_out << bw_down << endl;
                p = p->next;
            }

        }
        if(total_req == 8000){
            ofstream slot_out("./test17/pmslot8000.txt", ios::app);
            ofstream bw_out("./test17/pmbw8000.txt", ios::app);
            LinkNode* p = PM_LAYER;
            while(p != NULL){
                slot_out<<subtree_vmcap[g.nodeFromId(p->node)]<< endl;
                double bw_up = 0; double bw_down = 0;
                for(OutArcIt ait(g, parent_node[g.nodeFromId(p->node)]); ait != INVALID; ait++){
                    if(g.id(g.target(ait)) == p->node){
                        bw_up = arc_upload_cap[ait];
                        bw_down = arc_download_cap[ait];
                        break;
                    }
                }
                bw_out << bw_up << endl;
                bw_out << bw_down << endl;
                p = p->next;
            }

        }*/
/*
        if(total_req == 10000){
            ofstream slot_out("./test28/pmslot10000.txt", ios::app);
            ofstream bw_out("./test28/pmbw10000.txt", ios::app);
            LinkNode* p = PM_LAYER;
            while(p != NULL){
                slot_out<<subtree_vmcap[g.nodeFromId(p->node)]<< endl;
                double bw_up = 0; double bw_down = 0;
                for(OutArcIt ait(g, parent_node[g.nodeFromId(p->node)]); ait != INVALID; ait++){
                    if(g.id(g.target(ait)) == p->node){
                        bw_up = arc_upload_cap[ait];
                        bw_down = arc_download_cap[ait];
                        break;
                    }
                }
                bw_out << bw_up << endl;
                bw_out << bw_down << endl;
                p = p->next;
            }

        }*/
        /*if(total_req == 12000){
            ofstream slot_out("./test17/pmslot12000.txt", ios::app);
            ofstream bw_out("./test17/pmbw12000.txt", ios::app);
            LinkNode* p = PM_LAYER;
            while(p != NULL){
                slot_out<<subtree_vmcap[g.nodeFromId(p->node)]<< endl;
                double bw_up = 0; double bw_down = 0;
                for(OutArcIt ait(g, parent_node[g.nodeFromId(p->node)]); ait != INVALID; ait++){
                    if(g.id(g.target(ait)) == p->node){
                        bw_up = arc_upload_cap[ait];
                        bw_down = arc_download_cap[ait];
                        break;
                    }
                }
                bw_out << bw_up << endl;
                bw_out << bw_down << endl;
                p = p->next;
            }

        }*/
        total_req++;
/*
            if(1.0-s_util() >= 0.5 && 1.0-s_util() < 0.55){
                     if(t.sum_appvm_req < 7){
                        load_all[0]++;
                    }else if(t.sum_appvm_req < 9){
                        load_all[1]++;
                    }else if(t.sum_appvm_req < 11){
                        load_all[2]++;
                    }else if(t.sum_appvm_req < 13){
                        load_all[3]++;
                    }else
                        load_all[4]++;
                }*/
        //if(1.0-s_util() > 0.55) break;
        double acc = (double)accept_req/total_req;
        double util = 1.0-s_util();
        //ofstream file("./test25/acc_util.txt", ios::app);
        //file << acc << endl;
        //file << util << endl;
        if(util - acc > 0.01) break;
    }

    cout<<"Util Rate: " << 1.0-s_util()<<endl;
    cout<<"Accept Rate: " << (double)accept_req/total_req<<endl;
    //ofstream file("./test29/acc_util_without1200.txt", ios::app);
    //file <<(double)accept_req/total_req << endl;
    //ofstream file("./test27/acc_util_r3_16.txt", ios::app);
    //file <<(double)accept_req/total_req << endl;

            //ofstream file1("./test24/rej_rate.txt", ios::app);
        //for(int i = 0; i < 5; i++){
        //    file1 << load_rej[i]/load_all[i] << endl;
       // }
    cout << "allplace1/place2: " << all_place1_cnt<<"/"<<all_place2_cnt << endl;
    cout << "place1/place2: " << place1_cnt<<"/"<<place2_cnt << endl;
}

int main(int argc, const char * argv[])
{
    readGraph(argv);
    createTreeTopology();
    //cout << g.id(*(PM_LAYER->node))<< "carolz"<<endl;
    createTenantRequests();
    //cout << g.id(*(PM_LAYER->node))<< "carolz"<<endl;
    place();
    return 0;
}
