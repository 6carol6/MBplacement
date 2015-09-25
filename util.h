//
//  util.h
//  Created by wang xiaoliang on 4/3/14.
//  Copyright (c) 2014 wang xiaoliang. All rights reserved.
//

#ifndef MBplacement_util_h
#define MBplacement_util_h

#include <random>
#include <algorithm>
#include<ctime>

int uniformIntDist(int min_value, int max_value)
{
    //srand((unsigned int)time(0));
    return rand()/((double)RAND_MAX+1.0)*(max_value-min_value+1)+min_value;
}

#endif
