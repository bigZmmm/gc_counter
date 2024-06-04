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
#include "sys/time.h"
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
    /*1:oneof-combine后的状态 2:全是oneof 3：包括有or*/
    int type;
    int orlens;
    int lens;
    vector<oneof_item> oneof;
    ~ONEOFS(){
        oneof.clear();
    }
};

struct state_var{
    vector<int> vars; 
    int frequency;
};

class Counter
{
public:
    typedef std::vector<const Operator *> Plan;
    ONEOFS oneofs;
    int sum;
    Plan newplan;
    /*表示删除部分例子后的SMT无反例*/
    bool isfind;
    /*表示删除的例子是否能解*/
    bool counterissolvered;
    set<string> variables;
    vector<State*> counterset;
    vector<vector<State*>> planSet;

    vector<state_var> counterset_new;
    vector<string> everyplanvarset; 

    map<int,int> indextovar;
    long long belief_size;
    map<pair<int,int>,vector<PrePost>> axiomtovar;
    
    /*处理过的反例,如果重复三次处理这个,那么不再处理它,直到没有找到反例,再把他们放出来
    考虑最后怎么放,一次性放完,或者是一个个放
    */
    map<string,state_var> appearcounter;
    
    string init_smt;
    string regret_smt;
    string smt;
    string sasrestraint_smt;
    int total_counter;
public:
    Counter();
    ~Counter(){
        variables.clear();
    }
    set<string> getVariables(){
        return variables;
    }
    int getBelief_size(){
        return belief_size;
    }
    void printfhello(){
        cout<<"::"<<oneofs.type<<endl;
        if(oneofs.type==1){

        }else if(oneofs.type==2){

        }else if(oneofs.type==3){
            for(int i=0;i<oneofs.orlens;i++){
                int nowindex=0;
                cout<<"OR:"<<oneofs.oneof[i].len<<" ";
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
                cout<<endl;      
            }
            for(int i=0;i<oneofs.lens;i++){
                cout<<"231"<<endl;
                int index=i+oneofs.orlens;
                cout<<"ONEOF:"<<oneofs.oneof[index].len<<" ";
                int nowindex=0;
                for(int j=0;j<oneofs.oneof[index].len;j++){    
                    // cout<<oneofs.oneof[i].size[j]<<" ";
                    for(int k=0;k<oneofs.oneof[index].size[j];k++){
                        cout<<g_variable_name[oneofs.oneof[index].var[nowindex]]<<":"<<oneofs.oneof[index].val[nowindex];
                        if(k!=oneofs.oneof[index].size[j]-1)
                            cout<<",";
                        else
                            cout<<";";
                        nowindex++;
                    }
                }
                cout<<endl;      
            }
        }

        // if(oneofs.type==3)
        //     cout<<"ONEOF:";
        // for(int i=0;i<oneofs.lens;i++){
        //     if(!oneofs.type)
        //        cout<<"ONEOF:"<<oneofs.oneof[i].len<<" ";
        //     int nowindex=0;
        //     for(int j=0;j<oneofs.oneof[i].len;j++){    
        //         // cout<<oneofs.oneof[i].size[j]<<" ";
        //         for(int k=0;k<oneofs.oneof[i].size[j];k++){
        //             cout<<g_variable_name[oneofs.oneof[i].var[nowindex]]<<":"<<oneofs.oneof[i].val[nowindex];
        //             if(k!=oneofs.oneof[i].size[j]-1)
        //                 cout<<",";
        //             else
        //                 cout<<";";
        //             nowindex++;
        //         }
        //     }
        //     if(!oneofs.type)
        //         cout<<endl;      
        // }
    }
    int getTotal_counter(){
        return total_counter;
    }
    void initToSmt();
    bool conputerCounter(Plan plan);
    void addActionToGoal(Plan plan);
    string varToSmt(int var,int l,int i);
    void addRestraintToTime0();
    void addAxiomSmt(pair<int,int> vari,string *pre_smt,int timestep);
    void regretCurFact(const Operator *a,set<string> *preference_var,pair<int,int> now_facts,set<pair<int,int> > *new_facts,int time_stept);
    void optimizePlan(Plan plan);
    void optimizePlantest(Plan plan);
    bool invokeZ3();
    void clearAll(){
        init_smt.clear();
        init_smt.shrink_to_fit();
        regret_smt.clear();
        regret_smt.shrink_to_fit();
        smt.clear();
        smt.shrink_to_fit();
        sasrestraint_smt.clear();
        sasrestraint_smt.shrink_to_fit();
        variables.clear();
    }
};

#endif