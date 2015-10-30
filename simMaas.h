//
//  simMaas.h
//  implementation of Hadrian NSDI 2013
//  Created by wang xiaoliang on 4/2/14.
//  Copyright (c) 2014 wang xiaoliang. All rights reserved.
//

#ifndef MBplacement_simMaas_h
#define MBplacement_simMaas_h

#include <lemon/core.h>
#include <lemon/list_graph.h>
#include <lemon/lgf_reader.h>
#include <lemon/connectivity.h>
#include <lemon/preflow.h>
#include <lemon/elevator.h>
#include <lemon/circulation.h>
#include <lemon/path.h>
#include <lemon/dfs.h>

#include <set>
#include <map>
#include <list>
#include <vector>
#include <string>
#include <assert.h>
#include <memory.h>

using namespace lemon;
using namespace std;

typedef ListDigraph Digraph;
typedef Digraph::ArcIt ArcIt;
typedef Digraph::Arc Arc;
typedef Digraph::NodeIt NodeIt;
typedef Digraph::Node Node;
typedef Digraph::OutArcIt OutArcIt;
typedef Digraph::InArcIt InArcIt;

/// int maps for counting
typedef Digraph::ArcMap<int>     IntArcMap;
typedef Digraph::ArcMap<double>  DoubleArcMap;
typedef Digraph::NodeMap<int>    IntNodeMap;
typedef Digraph::NodeMap<double> DoubleNodeMap;
typedef Digraph::NodeMap<Node>   ParentNodeMap;

#define INT_MAX 0x7fffffff
#define TOTAL_MB_TYPE   2
#define DOUBLE_ZERO 0.0000000001
#define MB_TYPE_NUM_MIN 1
#define MB_TYPE_NUM_MAX 4

//PARAMETERA
#define BIN_MIN 500
#define BIN_MAX 1000
#define BEX_MIN 200
#define BEX_MAX 300
#define N_MIN 5
#define N_MAX 15
#define R_MIN 2
#define R_MAX 32
#define OPEN_TENANT_PER 10
#define DEP_OPEN_TENANT_PER 35 //+open
#define DEP_TENANT_PER 50 //+open+dep_open

#define MISSILE 1
#define TRAIN 0
#define TRUCK 0

enum MiddleboxType
{
    FW=0, RE, IDS, WANOPT
};

enum SwitchType
{
    CORE = -1,SPINE, LEAF, TOR, PM
};

enum ArcType
{
    CORESPINE, SPINELEAF, LEAFTOR, TORPM,
};

struct Placement{
    int             pm_id;
    int             amount;
    double          percentage;
    Placement*      next;
};

struct Tenant
{
    int              tenant_id;
    int              sum_appvm_req;
    int              sum_mb_req; //How many MBs all together
    int              min_load;
    int              external_load;
    bool             placement_success;
    Placement*       appvm_location;
    Placement*       mb_location[10];
    int              mb_req_num[10]; //How many MBs each type of MB?
    int              mb_type_num; //How many types of MBs?
    int              mv_ratio[10];
    int              R; //virtual R
    int              dep_num;
    set<int>         dependency;
};

struct LinkNode{
    int node;
    bool is_start;
    LinkNode* next;
};

typedef list<Tenant> Tenant_Request_Queue;


#endif
