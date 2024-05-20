#ifndef _COUNTER_H
#define _COUNTER_H

#include <cassert>
#include <iostream>
#include <string>
#include <vector>
#include <set>
#include "globals.h"
#include "state.h"
#include "z3++.h"
#include <z3++.h>
#include <map>
using namespace std;
struct oneof_item
{
    int len;
    vector<int> size;
    vector<int> var;
    vector<int> val;
    ~oneof_item(){
        size.clear();
        var.clear();
        val.clear();
    }
};

struct ONEOFS
{
    /*true:多个状态 false:多个oneof*/
    bool type;
    int lens;
    vector<oneof_item> oneof;
    ~ONEOFS(){
        oneof.clear();
    }
};

class Counter
{
    typedef std::vector<const Operator *> Plan;
    ONEOFS oneofs;
    set<string> variables;
    map<int,int> indextovar; 
    string init_smt;
    string regret_smt;
    string smt;
    string sasrestraint_smt;
public:
    Counter();
    ~Counter(){
        variables.clear();
    }
    set<string> getVariables(){
        return variables;
    }
    void printfhello(){
        if(oneofs.type)
            cout<<"ONEOF:";
        for(int i=0;i<oneofs.lens;i++){
            if(!oneofs.type)
               cout<<"ONEOF:"<<oneofs.oneof[i].len<<" ";
            int nowindex=0;
            for(int j=0;j<oneofs.oneof[i].len;j++){    
                // cout<<oneofs.oneof[i].size[j]<<" ";
                for(int k=0;k<oneofs.oneof[i].size[j];k++){
                    cout<<g_variable_name[oneofs.oneof[i].var[nowindex]]<<":"<<oneofs.oneof[i].val[nowindex];
                    if(k!=oneofs.oneof[i].size[j]-1)
                        cout<<",";
                    else
                        cout<<";";
                    nowindex++;
                }
            }
            if(!oneofs.type)
                cout<<endl;      
        }
    }
    void initToSmt();
    bool conputerCounter(Plan plan);
    void addActionToGoal(Plan plan);
    string varToSmt(int var,int l,int i);
    void addRestraintToTime0();
    void regretCurFact(const Operator *a,set<string> *preference_var,pair<int,int> now_facts,set<pair<int,int> > *new_facts,int time_stept);
};

#endif