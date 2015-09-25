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
//typedef Digraph::ArcMap<double>  DoubleArcMap;
typedef Digraph::NodeMap<int>    IntNodeMap;
//typedef Digraph::NodeMap<double> DoubleNodeMap;
typedef Digraph::NodeMap<Node>   ParentNodeMap;

#define INT_MAX 0x7fffffff
#define TOTAL_MB_TYPE   2


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
    Placement*      next;
};

struct Tenant
{
    int              tenant_id;
    int              sum_appvm_req;
    int              sum_mb_req;
    int              min_load;
    int              external_load;
    bool             placement_success;
    Placement*       appvm_location;
    Placement*       mb_location;
    int              mv_ratio;
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
