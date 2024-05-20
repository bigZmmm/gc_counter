#ifndef _Z3_COUNTER_H
#define _Z3_COUNTER_H

#include <iostream>
#include <sstream>
#include<vector>
#include<map>
#include"z3++.h"
#include<z3++.h>
using namespace z3;

class Z3_counter{
public:
    Z3_counter(){
        // cout<<"123"<<endl;   
    }
    ~Z3_counter(){
        // cout<<"234"<<endl;
    }
    bool extracCounter(std::string zmt,std::map<int,int> *sample);
};


#endif