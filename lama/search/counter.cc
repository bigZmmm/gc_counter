#include "counter.h"
#include "operator.h"
#include <cstdlib>
#include <string>
#include <vector>
#include <memory>
#include <cassert>
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <sys/times.h>
#include <climits>
#include <string.h>
#include <string>
#include <utility>
#include "z3_counter.h"
#include "state.h"
using namespace std;

string Counter::varToSmt(int var,int l,int i){
    string a = "",b = "";
    while(l>=0){
        char tmp = 48+l%10;
        a+=tmp;
        l/=10;
        if(l==0)
            break;
    }
    reverse(a.begin(),a.end());
    while(i>=0){
        char tmp = 48+i%10;
        b+=tmp;
        i/=10;
        if(i==0)
            break;
    }
    reverse(b.begin(),b.end());
    return g_variable_name[var]+"-"+a+"-"+b;
}

string stateToString(State* s){
    string tmp = "";
    for(int i=0;i<s->vars.size();i++){
        if(s->vars[i]!=(g_variable_domain[i]-1)){
            tmp+=to_string(i);
            tmp+="-";
            tmp+=to_string(s->vars[i]);
            tmp+='.';
        }
    }
    return tmp;
}

string stateToString2(state_var s){
    string tmp = "";
    for(int i=0;i<s.vars.size();i++){
        if(s.vars[i]!=(g_variable_domain[i]-1)){
            tmp+=to_string(i);
            tmp+="-";
            tmp+=to_string(s.vars[i]);
            tmp+='.';
        }
    }
    return tmp;
}

/*状态后移*/
void applyAction(state_var *predecessor, const Operator &op){
    /*test*/
    // for(int i=0;i<predecessor->vars.size();i++){
    //     cout<<g_variable_name[i]<<"-"<<predecessor->vars[i]<<endl;
    // }

    vector<Prevail> prevail = op.get_prevail();
    vector<PrePost> prepost = op.get_pre_post();
    
    bool isApply =true;
    /*第一步判断是否满足前置条件*/
    if(prevail.size()==0)
        isApply = true;
    else{
        for(int i=0;i<prevail.size();i++){
            if(prevail[i].prev!=predecessor->vars[prevail[i].var]){
                isApply = false;
                break;
            }
        }
    }
    //第二步,根据prepost,赋予新值
    vector<pair<int,int>> changevar;
    if(isApply)
    for(int i = 0; i < prepost.size(); i++) {
        int flag=true;
        for(int j = 0; j < prepost[i].cond.size(); j++){
            /*test*/
            // cout<<prepost[i].cond[j].prev<<"条件--状态"<<predecessor->vars[prepost[i].cond[j].var]<<endl;
            if(prepost[i].cond[j].prev!=predecessor->vars[prepost[i].cond[j].var]){
                flag=false;
                break;
            }
        }
        if((prepost[i].pre!=-1)&&(prepost[i].pre!=predecessor->vars[prepost[i].var]))
            flag=false;
        if(flag){
            // predecessor->vars[prepost[i].var] = prepost[i].post;
            changevar.push_back(pair<int,int>(prepost[i].var,prepost[i].post));
            /*test*/
            // cout<<"要改变的变量"<<i<<g_variable_name[prepost[i].var]<<"为"<<prepost[i].post<<endl;
        }
    }
    for(int i=0;i<changevar.size();i++){
        predecessor->vars[changevar[i].first] = changevar[i].second;
    }
    
    /*test*/
    // cout<<"动作后"<<endl;
    // for(int i=0;i<predecessor->vars.size();i++){
    //     cout<<g_variable_name[i]<<"-"<<predecessor->vars[i]<<endl;
    // }
}

void Counter::optimizePlanByConformant(Plan plan){
    int *samestate = new int[plan.size()+5];
    /*识别出oneof中*/
    ONEOFS curoneofs;
    curoneofs.lens = oneofs.lens;
    curoneofs.orlens = oneofs.orlens;
    curoneofs.oneof = oneofs.oneof;
    curoneofs.type = oneofs.type;


    delete samestate; 
}

Counter::Counter(){
    struct tms start, end;
    isfind=false;
    sum=0;
    total_counter=0;
    times(&start);
    /*找到vari与var对应下标*/
    for(int i = 0 ; i < g_variable_name.size() ; i++){
        string name = g_variable_name[i];
        int j=0,var=0,namesize = name.size();
        while(j<namesize){
            if(name[j]>=48&&name[j]<=57){
                var*=10;
                var+=(name[j]-48);
            }
            j++;
        }
        indextovar.insert(pair<int,int>(i,var));
    }
    oneofs.orlens=0;
    belief_size=1;
    /*读取oneof进入*/
    ifstream infile;
    infile.open("oneof", ios::in);
    string line;
    /*读取类型*/
    getline(infile, line);
    // cout<<line<<endl;
    if(line=="ORS")
        oneofs.type=1;
    else if(line=="OR")
        oneofs.type=3;
    else {
        oneofs.type=2;
    }
    cout<<oneofs.type<<endl;
    /*读取数量 针对于oneof和其他的读取*/
    getline(infile, line);
    istringstream ss(line);
    if(oneofs.type==3){
        ss >> oneofs.orlens;
        for(int i=0;i<oneofs.orlens;i++){
            oneof_item tmp;
            tmp.len=0;
            oneofs.oneof.push_back(tmp);
        }       
    }
    else{
        ss >> oneofs.lens;
        for(int i=0;i<oneofs.lens;i++){
            oneof_item tmp;
            tmp.len=0;
            oneofs.oneof.push_back(tmp);
        }   
    }
    int index=0,andsize=0,prevar=-1;
    while(getline(infile, line)){
        // cout<<line<<endl;
        if(line==", "){
            oneofs.oneof[index].size.push_back(andsize);
            andsize=0;
        }
        if(line=="ONEOF"){
            getline(infile, line);
            istringstream ss(line);
            ss >> oneofs.lens;
            for(int i=0;i<oneofs.lens;i++){
                oneof_item tmp;
                tmp.len=0;
                oneofs.oneof.push_back(tmp);
            }
        }
        else if(line=="END_ONEOF"||line=="END_OR"||(line==", "&&oneofs.type==1)){
            oneofs.oneof[index].len = oneofs.oneof[index].size.size();
            // cout<<index<<"-"<<oneofs.oneof[index].len<<endl;
            index++;
        }
        else if(line!=", "){
            andsize++;
            int var,val;
            var = -1;		
            for(int i = 0 ; i < g_variable_name.size() ; i++)
            {
                /*读取的name后面有一个空格，长度会+1*/
                if(line.find(g_variable_name[i]) == 0 && line.size() == g_variable_name[i].size()+1)
                {
                    var = i;
                    // cout << g_variable_name[i]<<" ";
                }
            }
            getline(infile, line);
            stringstream ss(line);
            ss >> val;
            // if(val==-1){
            //     val = g_variable_domain[var]-1;
            // }
            if (var!=-1) {
                /*var：对应g_variable_name下标,val：该变量的值*/
                oneofs.oneof[index].var.push_back(var);
                oneofs.oneof[index].val.push_back(val);
            } 
        }
    }
    
    /*计算信仰状态数量*/
    if(oneofs.type==2)
        belief_size=oneofs.lens;
    else
    for(int i=0;i<oneofs.lens;i++){
        belief_size*=oneofs.oneof[i].len;
    }
    /*保存axiom*/
    /*如果有axiom，要添加axiom的约束*/
    for(int i=0;i<g_axioms.size();i++){
        vector<PrePost> prepost = g_axioms[i].get_pre_post();
        for(int j=0;j<prepost.size();j++){
            pair<int,int> vari = pair<int,int>(prepost[j].var,prepost[j].post);
            if(axiomtovar.find(vari)==axiomtovar.end()){
                vector<PrePost> now;
                axiomtovar.insert(pair<pair<int,int>,vector<PrePost>>(vari,now));
            }
            axiomtovar[vari].push_back(prepost[j]);
        }
    }
    cout<<"axiom:"<<axiomtovar.size()<<endl;
    for(auto ot : axiomtovar){
        for(int i=0;i<ot.second.size();i++){
            cout<<"(-["<<ot.second[i].var<<","<<ot.second[i].pre<<"]-";
            for(int j=0;j<ot.second[i].cond.size();j++){
                cout<<"["<<ot.second[i].cond[j].var<<","<<ot.second[i].cond[j].prev<<"]-";
            }
            cout<<")"<<endl;
        }
        cout<<"->["<<ot.first.first<<"-"<<ot.first.second<<"]"<<endl;
    }
    // for(int i = 0 ; i < g_variable_name.size() ; i++){
    //     cout<<indextovar[i]<<" "<<i<<endl;
    // }
    times(&end);
    int total_ms = (end.tms_utime - start.tms_utime) * 10;
    total_counter+=total_ms;
}

/*不再使用*/
void Counter::optimizePlan(Plan plan){
    /*test*/
    // cout<<"修改前规划长度:"<<plan.size()<<endl;
    // for(int i=0;i<plan.size();i++){
    //     cout<<plan[i]->get_name()<<" ";        
    // }
    int plansize = plan.size(),countersize = counterset.size();
    int planrepeat[plansize+10]={0};
    /*test*/
    for(int i=counterset.size()-1;i>counterset.size()-3;i--){
        cout<<i<<"次"<<endl;
        counterset[i]->dump();
        cout<<stateToString(counterset[i])<<endl;
    }
    planSet.push_back(counterset);
    int now = 0;
    for(int i=0;i<plansize;i++){
        vector<State*> curCounterset;
         /*所有的状态后移*/
        // cout<<plan[i]->get_name()<<":"<<endl;
        for(int j=0;j<countersize;j++){
            State* curState = new State();
            int h;
            for(h=0;h<g_operators.size();h++)
            {
                if(g_operators[h].get_name().compare(plan[i]->get_name()) == 0) break;
            }
            // curState = new State(*planSet[i][j],g_operators[h]);
            // planSet[i][j]->dump();
            curState->assign(State(*planSet[i][j],g_operators[h]));
            // curState->dump();
            // planSet[i][j]->dump();
            // planSet[i][j]->dump();
            curCounterset.push_back(curState);
        }
        planSet.push_back(curCounterset);
        /*后移后，判断是否有与之前相同的状态*/
        // cout<<"size:"<<curCounterset.size()<<endl;
        for(int j=0;j<=i;j++){
            /*每次规划中的都要遍历一次*/
            bool isidentical = true;
            for(int k=0;k<countersize;k++){
                // curCounterset[k]->dump();
                // cout<<curCounterset[k]->isOneState(*planSet[j][k])<<endl;
                if(!curCounterset[k]->isOneState(*planSet[j][k])){
                    isidentical=false;
                    break;
                }
            }
            if(isidentical){
                cout<<"这里有相同的状态"<<j<<"->"<<(i+1)<<endl;
                planrepeat[j]=i+1;
                now++;
            }
        }
    }
    
    /*test*/
    // for(int i=0;i<countersize;i++){
    //     cout<<i<<endl;
    //     planSet[plansize][i]->dump();
    // }

    for(int i=0;i<plansize+1;i++){
        string tmp="";
        for(int j=0;j<countersize;j++){
            tmp+=stateToString(planSet[i][j]);
        }
        cout<<tmp<<endl;
    }

    for(int i=0;i<plansize+1;i++){
        cout<<planrepeat[i]<<" ";
    }
    for(int i=0;i<plansize+1;i++){
        if(i>0){
            newplan.push_back(plan[i-1]);
        }
        /*将动作往后移动*/
        while(planrepeat[i]>i){
            i = planrepeat[i];
        }  

    }
    cout<<"重复的次数："<<now<<endl;
    sum+=now;
    // cout<<endl;
    // conputerCounter(newplan);

    for(int i=0;i<planSet.size();i++){
        // State* curState;
        // for(int j=0;j<planSet[i].size();j++){
        //     curState =planSet[i][j];
        //     delete curState;
        // }
        planSet[i].clear();
        planSet[i].shrink_to_fit();
    }
    planSet.clear();
    planSet.shrink_to_fit();

}

// 需要根据一致性初始状态进行简化，否则每次迭代的规划解会失去对整个初始状态的一般性
// 待修改
void Counter::optimizePlantest(Plan plan){
    /*test*/
    // cout<<"修改前规划长度:"<<plan.size()<<endl;
    // for(int i=0;i<plan.size();i++){
    //     cout<<plan[i]->get_name()<<" ";        
    // }
    // 初始反例集要和map中的一样
    
    int plansize = plan.size(),countersize = counterset_new.size();
    int planrepeat[plansize+10]={0};
    vector<state_var> curStates;
    curStates = counterset_new;
    string statesstring="";
    
    for(int i=0;i<countersize;i++){
        statesstring+=stateToString2(curStates[i]);
    }
    // cout<<statesstring<<endl;
    everyplanvarset.push_back(statesstring);
    statesstring="";
    int now = 0;
    for(int i=0;i<plansize;i++){
         /*所有的状态后移*/
        // cout<<plan[i]->get_name()<<":"<<endl;
        for(int j=0;j<countersize;j++){
            int h;
            for(h=0;h<g_operators.size();h++)
            {
                if(g_operators[h].get_name().compare(plan[i]->get_name()) == 0) break;
            }
            applyAction(&curStates[j],g_operators[h]);
            statesstring+=stateToString2(curStates[j]);
        }
        everyplanvarset.push_back(statesstring);
        
        /*后移后，判断是否有与之前相同的状态*/
        // cout<<"size:"<<curCounterset.size()<<endl;
        for(int j=0;j<=i;j++){
            /*每次规划中的都要遍历一次*/
            bool isidentical = true;
            if((statesstring.size()==everyplanvarset[j].size())&&(statesstring.compare(everyplanvarset[j])==0)){
                // cout<<"这里有相同的状态"<<j<<"->"<<(i+1)<<endl;
                planrepeat[j]=i+1;
                now++;
            }
        }
        statesstring="";
    }
    
    /*test*/
    // for(int i=0;i<countersize;i++){
    //     cout<<i<<endl;
    //     planSet[plansize][i]->dump();
    // }
    // cout<<everyplanvarset[plansize]<<endl;
    cout<<endl;
    // for(int i=0;i<plansize+1;i++){
    //     cout<<everyplanvarset[i]<<endl;
    // }
    /*再对目标状态运用axiom*/
    for(int k=0;k<curStates.size();k++){
        for(auto ot : axiomtovar){
            bool issatisfy=false;
            /*如果满足其中一个，那么就会break出来*/
            for(int i=0;i<ot.second.size();i++){
                // cout<<"(-["<<ot.second[i].var<<","<<ot.second[i].pre<<"]-";
                if(curStates[k].vars[ot.second[i].var]!=ot.second[i].pre)
                    continue;
                int assessnum=0;
                for(int j=0;j<ot.second[i].cond.size();j++){
                    // cout<<"["<<ot.second[i].cond[j].var<<","<<ot.second[i].cond[j].prev<<"]-";
                    if(curStates[k].vars[ot.second[i].cond[j].var]==ot.second[i].cond[j].prev)
                        assessnum++;
                }
                // cout<<")"<<endl;
                if(assessnum==ot.second[i].cond.size()){
                    issatisfy=true;
                    break;
                }
                
            }
            if(issatisfy)
                curStates[k].vars[ot.first.first] = ot.first.second;
            // cout<<"->["<<ot.first.first<<"-"<<ot.first.second<<"]"<<endl;
        }
    }

    /*遍历curstate_验证是否为有效解*/
    int isvalidplan=true;
    for(int i=0;i<curStates.size();i++){
        for(int j=0;j<g_goal.size();j++){
            /*test*/
            // cout<<"当前对比:"<<curStates[i].vars[g_goal[j].first]<<"与"<<g_goal[j].second<<endl;
            if(curStates[i].vars[g_goal[j].first]!=g_goal[j].second)
                isvalidplan=false;
        }

    }
    
    if(isvalidplan){
        cout<<"规划解能解反例集！"<<endl;
        counterissolvered=true;
    }else{
        cout<<"规划解还不能解反例集！"<<endl;
        counterissolvered=false;
    }
    cout<<endl;
    for(int i=0;i<plansize+1;i++){
        cout<<planrepeat[i]<<" ";
    }
    for(int i=0;i<plansize+1;i++){
        if(i>0){
            newplan.push_back(plan[i-1]);
        }
        /*将动作往后移动*/
        while(planrepeat[i]>i){
            i = planrepeat[i];
        }  
    }
    cout<<"重复的次数："<<now<<endl;
    cout<<"规划解长度"<<newplan.size()<<endl;
    sum+=now;
    // cout<<endl;
    // conputerCounter(newplan);
    everyplanvarset.clear();
    everyplanvarset.shrink_to_fit();
}

/*在生成oneof和or时，为实现其中的not a，如果为负数，则为not（var=val）
,为了避开val=0这一情况，在编译时将值减小1，这里再加上1为正确值*/
void Counter::initToSmt(){
    init_smt="(assert (and\n";
    /*1.转换初始状态的SMT公式，并且记录所有的变量*/
    // dump_everything();
    int var_len = g_initial_state->vars.size();
    /*识别其中每个状态都相同的fact*/
    int *isunKnownFact = (int*)calloc(var_len,sizeof(int));
    memset(isunKnownFact,0,var_len);
    /*多种状态的oneof*/
    if(oneofs.type==1){
        /*第一次循环，识别known_fact*/
        for(int i=0;i<oneofs.lens;i++){
            int nowindex=0;
            for(int j=0;j<oneofs.oneof[i].len;j++){
                for(int k=0;k<oneofs.oneof[i].size[j];k++){
                    isunKnownFact[oneofs.oneof[i].var[nowindex]]=1;
                    /*为unkonwn的fact初始一定要设置为假的*/
                    // g_initial_state->set_var(oneofs.oneof[i].var[nowindex],oneofs.oneof[i].val[nowindex]);
                    g_initial_state->negate_var(oneofs.oneof[i].var[nowindex]);
                    nowindex++;
                }
            }
        }
        int state_size=0;
        /*添加known_fact,但要确保不是axiom*/
        for(int i=0;i<var_len;i++){
            if(isunKnownFact[i]==0){
                // cout<<"123:"<<(axiomtovar.find(pair<int,int>(i,g_initial_state->vars[i]))==axiomtovar.end())<<endl;
                if(axiomtovar.find(pair<int,int>(i,g_initial_state->vars[i]))==axiomtovar.end()){
                    string var0 = varToSmt(i,g_initial_state->vars[i],0);
                    variables.insert(var0);
                    init_smt+=" ";
                    init_smt+=var0;
                    init_smt+="\n";
                }
            }else{
                state_size++;
            }
        }
        /*所有状态对应的SMT*/
        vector<string> all_state;
        /*构建oneof的SMT*/
        string first_or=" (or ";
        for(int i=0;i<oneofs.lens;i++){
            int nowindex=0;
            for(int k=0;k<oneofs.oneof[i].len;k++){
                string tmp="";
                if(state_size>1)
                tmp+="(and ";
                for(int j=0;j<oneofs.oneof[i].size[k];j++){
                    g_initial_state->set_var(oneofs.oneof[i].var[nowindex],oneofs.oneof[i].val[nowindex]);
                    nowindex++;
                }
                for(int j=0;j<var_len;j++){
                    if(isunKnownFact[j]){
                        string var0 = varToSmt(j,g_initial_state->vars[j],0);
                        tmp+=var0;
                        if((j!=var_len-1)&&(state_size>1))
                            tmp+=" ";
                        variables.insert(var0);
                    }
                }
                if(state_size>1)
                tmp+=")";
                for(int j=0;j<oneofs.oneof[i].size[k];j++){
                    g_initial_state->negate_var(oneofs.oneof[i].var[nowindex-j-1]);
                }
                // cout<<endl<<tmp;
                first_or+=tmp;
                first_or+=" ";
                all_state.push_back(tmp);
            }
        }
        first_or+=")";
        init_smt+=first_or;
        init_smt+="\n";
        g_initial_state->vars = g_original_values;
        /*构建所有的oneof约束*/
        for(int i=0;i<oneofs.lens-1;i++){
            int j=i+1;
            do{
                string else_or=" (or ";
                else_or+="(not ";
                else_or+=all_state[i];
                else_or+=") ";
                else_or+="(not ";
                else_or+=all_state[j];
                else_or+="))";
                init_smt+=else_or;
                init_smt+="\n";
                j++;
            }while(j<oneofs.lens);
        }
        
    }else{
        
        /*第一次循环，识别known_fact，oneof和or中没有的则为known_fact*/
        /*先识别or中的*/
        for(int i=0;i<oneofs.orlens;i++){
            int nowindex=0;
            /*识别or中的*/
            for(int j=0;j<oneofs.oneof[i].len;j++){
                for(int k=0;k<oneofs.oneof[i].size[j];k++){
                    isunKnownFact[oneofs.oneof[i].var[nowindex]]=1;
                    nowindex++;
                }
            }
        }
        
        /*再识别oneof中的*/
        for(int i=0;i<oneofs.lens;i++){
            int nowindex=0;
            int index = oneofs.orlens+i;
            /*识别or中的*/
            for(int j=0;j<oneofs.oneof[index].len;j++){
                for(int k=0;k<oneofs.oneof[index].size[j];k++){
                    isunKnownFact[oneofs.oneof[index].var[nowindex]]=1;
                    nowindex++;
                }
            }
        }
        int state_size=0;
        /*添加known_fact*/
        for(int i=0;i<var_len;i++){
            if(isunKnownFact[i]==0){
                if(axiomtovar.find(pair<int,int>(i,g_initial_state->vars[i]))==axiomtovar.end()){
                    string var0 = varToSmt(i,g_initial_state->vars[i],0);
                    variables.insert(var0);
                    // cout<<var0<<endl;
                    init_smt+=" ";
                    init_smt+=var0;
                    init_smt+="\n";
                }
            }else{
                state_size++;
            }
        }
        /*遍历所有的oneof,生存oneof的smt代码*/
        for(int i=0;i<oneofs.lens+oneofs.orlens;i++){
            int nowindex;
            /*判断是否oneof里面参数的变量都是一样的，只需要判定第一个每个oneof中的第一个var*/
            int is1var = true;
            nowindex = oneofs.oneof[i].size[0];
            for(int j=1;j<oneofs.oneof[i].len;j++){
                // cout<<oneofs.oneof[i].var[nowindex]<<"--_--"<<oneofs.oneof[i].var[nowindex-oneofs.oneof[i].size[j-1]]<<endl;
                if(oneofs.oneof[i].var[nowindex]!=oneofs.oneof[i].var[nowindex-oneofs.oneof[i].size[j-1]]||oneofs.oneof[i].size[j]>1){
                    is1var=false;
                    break;
                }
                nowindex+=oneofs.oneof[i].size[j];
            }
            
            /*所有状态对应的SMT*/
            vector<string> all_state;
            /*构建oneof的SMT*/
            // cout<<"is1var:"<<is1var<<endl;
            string first_or=" (or ";
            nowindex=0;
            for(int j=0;j<oneofs.oneof[i].len;j++){
                string tmp="";
                /*构造oneof的初始SMT*/
                if(!is1var&&oneofs.type==2){
                    tmp+="(and ";
                    nowindex=0;
                    for(int k=0;k<oneofs.oneof[i].len;k++){
                        for(int m=0;m<oneofs.oneof[i].size[k];m++){
                            string var0="";
                            if(k==j){
                                if(oneofs.oneof[i].val[nowindex]<0){
                                    var0+=varToSmt(oneofs.oneof[i].var[nowindex],-(oneofs.oneof[i].val[nowindex]+1),0);
                                }
                                else
                                    var0+=varToSmt(oneofs.oneof[i].var[nowindex],oneofs.oneof[i].val[nowindex],0);
                            }else{
                                var0+=varToSmt(oneofs.oneof[i].var[nowindex],g_variable_domain[oneofs.oneof[i].var[nowindex]]-1,0);
                            }
                            variables.insert(var0);
                            if((k==j)&&(oneofs.oneof[i].val[nowindex]<0))
                                tmp+="(not ";
                            tmp+=var0;
                            if((k==j)&&(oneofs.oneof[i].val[nowindex]<0))
                                tmp+=")";
                            tmp+=" ";
                            nowindex++;
                        }
                    }
                    tmp+=")";
                }
                else if(is1var||oneofs.type==3)
                    for(int m=0;m<oneofs.oneof[i].size[j];m++){
                        string var0="";
                        if(oneofs.oneof[i].val[nowindex]<0)
                            var0+=varToSmt(oneofs.oneof[i].var[nowindex],-(oneofs.oneof[i].val[nowindex]+1),0);
                        else
                            var0+=varToSmt(oneofs.oneof[i].var[nowindex],oneofs.oneof[i].val[nowindex],0);
                        variables.insert(var0);
                        if(oneofs.oneof[i].val[nowindex]<0)
                            tmp+="(not ";
                        tmp+=var0;
                        if(oneofs.oneof[i].val[nowindex]<0)
                            tmp+=")";
                        tmp+=" ";
                        nowindex++;
                    }
                first_or+=tmp;
                first_or+=" ";
                if(i>=oneofs.orlens)
                all_state.push_back(tmp);
            }
            first_or+=")";
            // cout<<first_or<<endl;
            init_smt+=first_or;
            init_smt+="\n";
            if(i>=oneofs.orlens)
            for(int j=0;j<oneofs.oneof[i].len-1;j++){
                int k=j+1;
                do{
                    string else_or=" (or ";
                    else_or+="(not ";
                    else_or+=all_state[j];
                    else_or+=") ";
                    else_or+="(not ";
                    else_or+=all_state[k];
                    else_or+="))";
                    init_smt+=else_or;
                    init_smt+="\n";
                    k++;
                }while(k<oneofs.oneof[i].len);
            }
            all_state.clear();
        }
        /*添加状态大于1的初始反例*/
        if(!isfind)
        for(map<string,state_var>::iterator t=appearcounter.begin();t!=appearcounter.end();t++){
            if(t->second.frequency>1){
                string forbiden_initial=" (not (and ";
                for(int i=0;i<t->second.vars.size();i++){
                    if(isunKnownFact[i]){
                        forbiden_initial+=varToSmt(i,t->second.vars[i],0);
                        forbiden_initial+=" ";
                    }
                }
                forbiden_initial+="))";
                init_smt+=forbiden_initial;
                init_smt+="\n";
            }
        }

    }
    // cout<<endl<<variables.size()<<endl;
    init_smt+="))";
    // cout<<endl<<init_smt;
    delete isunKnownFact;
}

void Counter::addAxiomSmt(pair<int,int> vari,string *pre_smt,int timestep){

}

void Counter::regretCurFact(const Operator *a,set<string> *preference_var,pair<int,int> now_facts,set<pair<int,int> > *new_facts,int time_step){
    // cout<<a->get_name()<<"--"<<g_variable_name[now_facts.first] << ": " << now_facts.second<<" "<<time_step<<endl;
    string fact_regret_smt="(or ",add_smt = "(or false ",notdel_smt="(not (or false ";
    string cur_fact = varToSmt(now_facts.first,now_facts.second,time_step);
    string now_fact = varToSmt(now_facts.first,now_facts.second,time_step-1);
    variables.insert(now_fact);
    new_facts->insert(now_facts);
    vector<PrePost> prepost = a->get_pre_post();
    vector<Prevail> prevail = a->get_prevail();
    
    /*这里还要添加满足前置条件，才能保证这个谓语是，满足这个动作，不然会出现，不满足这个动作的前置条件，但是满足条件影响*/
    /*满足前置条件并且满足条件影响，才能被添加或者被删除*/
    for(int i=0;i<prepost.size();i++){
        if(a->isadd(now_facts.first,now_facts.second,i)){
            if(prepost[i].cond.size()+prevail.size()>1)
                    add_smt+="(and ";
            if(prepost[i].cond.size()>0||prevail.size()>0){
                for(int j=0;j<prepost[i].cond.size();j++){
                    string vari = varToSmt(prepost[i].cond[j].var,prepost[i].cond[j].prev,time_step-1);
                    variables.insert(vari);
                    add_smt+= vari;
                    add_smt+=" ";
                    new_facts->insert(pair<int,int>(prepost[i].cond[j].var,prepost[i].cond[j].prev));
                }
                /*还需要添加前置条件*/
                for(int j=0;j<prevail.size();j++){
                    string vari = varToSmt(prevail[j].var,prevail[j].prev,time_step-1);
                    // preference_var->insert(vari);
                    variables.insert(vari);
                    add_smt+= vari;
                    add_smt+=" ";
                    new_facts->insert(pair<int,int>(prevail[j].var,prevail[j].prev));
                }
            }
            else{
                add_smt+= "true";
                add_smt+=" ";
            }
            if(prepost[i].cond.size()+prevail.size()>1)
                add_smt+=") ";
        }
        if(a->isdel(now_facts.first,now_facts.second,i)){
            if(prepost[i].cond.size()+prevail.size()>1)
                    notdel_smt+="(and ";
            if(prepost[i].cond.size()>0||prevail.size()>0){
                for(int j=0;j<prepost[i].cond.size();j++){
                    string vari = varToSmt(prepost[i].cond[j].var,prepost[i].cond[j].prev,time_step-1);
                    variables.insert(vari);
                    notdel_smt+= vari;
                    notdel_smt+=" ";
                    new_facts->insert(pair<int,int>(prepost[i].cond[j].var,prepost[i].cond[j].prev));
                }   
                /*还需要添加前置条件*/
                for(int j=0;j<prevail.size();j++){
                    string vari = varToSmt(prevail[j].var,prevail[j].prev,time_step-1);
                    // preference_var->insert(vari);
                    variables.insert(vari);
                    notdel_smt+= vari;
                    notdel_smt+=" ";
                    new_facts->insert(pair<int,int>(prevail[j].var,prevail[j].prev));
                }
            }
            else{
                notdel_smt+= "true";
                notdel_smt+=" ";
            }
            if(prepost[i].cond.size()+prevail.size()>1)
                notdel_smt+=") ";
        }
    }
    add_smt+=")";
    notdel_smt+="))";
    // cout<<"add:"<<add_smt<<" del:"<<notdel_smt<<endl<<endl;
    /*提取回归的前置条件*/
    // for(int i=0;i<prevail.size();i++){
    //     string vari = varToSmt(prevail[i].var,prevail[i].prev,time_step-1);
    //     preference_var->insert(vari);
    //     variables.insert(vari);
    //     new_facts->insert(pair<int,int>(prevail[i].var,prevail[i].prev));
    // }
    fact_regret_smt+="(and ";
    fact_regret_smt+=add_smt;
    fact_regret_smt+=" ";
    fact_regret_smt+=notdel_smt;
    fact_regret_smt+=") ";
    fact_regret_smt+="(and ";
    fact_regret_smt+=now_fact;
    fact_regret_smt+=" ";
    fact_regret_smt+=notdel_smt;
    fact_regret_smt+="))";

    regret_smt+=" (= ";
    regret_smt+=cur_fact;
    regret_smt+=" ";
    regret_smt+=fact_regret_smt;
    regret_smt+=")\n";
    // cout<<regret_smt<<endl;

}

void Counter::addActionToGoal(Plan plan){
    // dump_everything();
    regret_smt = "(assert (and true ";
    string preference = " (not (and ";
    set<string> preference_var;
    set<pair<int,int> > now_facts;
    set< pair<int,int> > new_facts;
    int plan_size = plan.size();
    /*添加目标状态:*/
    for(int i = 0; i < g_goal.size(); i++){
        string var_goal = varToSmt(g_goal[i].first,g_goal[i].second,plan_size);
        preference_var.insert(var_goal);
        variables.insert(var_goal);
        now_facts.insert(pair<int, int>(g_goal[i].first, g_goal[i].second));
        
    }
    for(auto now_fact:now_facts){
        // cout<<now_fact.first<<" "<<now_fact.second<<endl;
        new_facts.insert(now_fact);
        if(axiomtovar.find(now_fact)!=axiomtovar.end()){
            vector<PrePost> pre_post = axiomtovar[now_fact];
            string vari = varToSmt(now_fact.first,now_fact.second,plan_size);
            variables.insert(vari);
            string axiom_smt="(= ";
            axiom_smt+=vari;
            axiom_smt+=" (or ";
            for(int i=0;i<pre_post.size();i++){
                string one_axiom="(and ";
                string varj = varToSmt(pre_post[i].var,pre_post[i].pre,plan_size);
                // variables.insert(varj);
                // one_axiom+=varj;
                // one_axiom+=" ";
                // new_facts.insert(pair<int,int>(pre_post[i].var,pre_post[i].pre));
                // cout<<"(-["<<ot.second[i].var<<","<<ot.second[i].pre<<"]-";
                for(int j=0;j<pre_post[i].cond.size();j++){
                    varj = varToSmt(pre_post[i].cond[j].var,pre_post[i].cond[j].prev,plan_size);
                    variables.insert(varj);
                    one_axiom+=varj;
                    one_axiom+=" ";
                    new_facts.insert(pair<int,int>(pre_post[i].cond[j].var,pre_post[i].cond[j].prev));
                    // cout<<"["<<ot.second[i].cond[j].var<<","<<ot.second[i].cond[j].prev<<"]-";
                }
                one_axiom+=") ";
                axiom_smt+=one_axiom;
                // cout<<")"<<endl;
            }
            axiom_smt+="))\n";
            // cout<<axiom_smt<<endl;
            regret_smt+=axiom_smt;
            // cout<<"->["<<ot.first.first<<"-"<<ot.first.second<<"]"<<endl;
        }
    }
    now_facts.clear();
    now_facts=new_facts;
    new_facts.clear();
    /*从目标状态开始进行回归*/
    for(int i=plan_size-1;i>=0;i--){
        /*对nowfact添加axiom*/
         /*添加axiom*/
        //  cout<<"size:"<<now_facts.size()<<endl;
        
        for(set<pair<int, int> >::iterator iter=now_facts.begin(); iter!=now_facts.end(); iter++){
            regretCurFact(plan[i],&preference_var,pair<int,int>(iter->first,iter->second),&new_facts,i+1);
        }
        now_facts.clear();
        for(auto new_fact:new_facts){
            // cout<<now_fact.first<<" "<<now_fact.second<<endl;
            now_facts.insert(new_fact);
            if(axiomtovar.find(new_fact)!=axiomtovar.end()){
                vector<PrePost> pre_post = axiomtovar[new_fact];
                string vari = varToSmt(new_fact.first,new_fact.second,i+1);
                variables.insert(vari);
                string axiom_smt="(= ";
                axiom_smt+=vari;
                axiom_smt+=" (or ";
                for(int k=0;k<pre_post.size();k++){
                    string one_axiom="(and ";
                    string varj = varToSmt(pre_post[k].var,pre_post[k].pre,i+1);
                    // variables.insert(varj);
                    // one_axiom+=varj;
                    // one_axiom+=" ";
                    // now_facts.insert(pair<int,int>(pre_post[k].var,pre_post[k].pre));
                    // cout<<"(-["<<ot.second[i].var<<","<<ot.second[i].pre<<"]-";
                    for(int j=0;j<pre_post[k].cond.size();j++){
                        varj = varToSmt(pre_post[k].cond[j].var,pre_post[k].cond[j].prev,i+1);
                        variables.insert(varj);
                        one_axiom+=varj;
                        one_axiom+=" ";
                        now_facts.insert(pair<int,int>(pre_post[k].cond[j].var,pre_post[k].cond[j].prev));
                        // cout<<"["<<ot.second[i].cond[j].var<<","<<ot.second[i].cond[j].prev<<"]-";
                    }
                    one_axiom+=") ";
                    axiom_smt+=one_axiom;
                    // cout<<")"<<endl;
                }
                axiom_smt+="))\n";
                // cout<<axiom_smt<<endl;
                regret_smt+=axiom_smt;
                // cout<<"->["<<ot.first.first<<"-"<<ot.first.second<<"]"<<endl;
            }
        }
        new_facts.clear();
    }
    /*回归完，对preference进行拼接*/
    for(set<string>::iterator iter=preference_var.begin(); iter!=preference_var.end(); iter++){
        preference+=*iter;
        preference+="\n ";
    }
    preference+=" ))\n";
    regret_smt+=preference;
    regret_smt+="))";
    // cout<<regret_smt<<endl;

    // cout<<"规划长度："<<plan.size()<<endl;
    // for(int i=0;i<plan.size();i++){
    //     cout<<plan[i]->get_name()<<" ";
    // }
    // cout<<endl;
}

void Counter::addRestraintToTime0(){
    sasrestraint_smt = "(assert (and ";
    for(int i=0;i<g_variable_domain.size();i++){
        string ors=" (or ";
        for(int j=0;j<g_variable_domain[i]-1;j++){
            string var0 = varToSmt(i,j,0);
            for(int k=j+1;k<g_variable_domain[i];k++){
                string tmp = " (or (not ";
                string var1 = varToSmt(i,k,0);
                tmp +=var0;tmp+=") (not ";
                tmp+=var1;tmp+="))\n";
                sasrestraint_smt+=tmp;
                variables.insert(var1);
            }
            ors+=var0;ors+=" ";
            variables.insert(var0);
        }
        string var0 = varToSmt(i,g_variable_domain[i]-1,0);
        variables.insert(var0);
        ors+=var0;ors+=")\n";
        sasrestraint_smt+=ors;
    }
    sasrestraint_smt+="))";
    // cout<<sasrestraint_smt<<endl;
}

bool Counter::invokeZ3(){
     /*调用z3求解器求反例，并且进行提取*/
    map<int,int> sample;
    Z3_counter *zz = new Z3_counter();
    bool isFind = zz->extracCounter(smt,&sample);
    
    // cout<<"修改前："<<endl;
    // for(int i = 0 ; i < g_variable_name.size() ; i++){
    //     cout<<g_variable_name[i]<<" "<<g_initial_state->vars[i]<<endl;
    // }
    cout<<isFind<<endl;
    if(isFind){
        isfind=false;
        for(int i=0;i<g_initial_state->vars.size();i++){
          int var = indextovar[i];
          if(sample.find(var)!=sample.end())
              g_initial_state->set_var(i,sample[var]);
        }
        // cout<<"修改后："<<endl;
        // for(int i = 0 ; i < g_variable_name.size() ; i++){
        //     cout<<g_variable_name[i]<<" "<<g_initial_state->vars[i]<<endl;
        // }  
    
        /*test*/
        // cout<<"hear"<<endl;
        /*将之前的反例保存,如果出现多次,那么加入*/
        string statestring = stateToString(g_initial_state);
        if(appearcounter.find(statestring)==appearcounter.end()){
            state_var tmp;
            tmp.frequency=1;
            tmp.vars = g_initial_state->vars;
            appearcounter.insert(pair<string,state_var>(statestring,tmp));
            /*不出现多次才能保存*/
            counterset_new.push_back(tmp);
        }else{
            appearcounter[statestring].frequency++;
            cout<<"已经出现过"<<endl;
            /*如果出现过，那么再重新计算反例*/
            // return invokeZ3();
        }
        /*test*/
        int k=1;
        for(map<string,state_var>::iterator t=appearcounter.begin();t!=appearcounter.end();t++){
            cout<<"状态"<<k<<"出现在反例集中的次数："<<t->second.frequency<<endl;
            k++;
        }
        delete zz;
        return true;
    }else{
        /*如果没有找到反例了，再放开约束看一下*/
        /*则再对约束中的n个进行求解*/
        if(!isfind){
            isfind=true;
            // initToSmt();
            // smt="";
            // for(set<string>::iterator iter=variables.begin(); iter!=variables.end(); iter++){
            //     smt+="(declare-const ";
            //     smt+=*iter;
            //     smt+=" Bool)\n";
            // }
            // smt+=init_smt;
            // smt+=regret_smt;
            // smt+=sasrestraint_smt;
            // isFind = zz->extracCounter(smt,&sample);
            // cout<<isFind<<endl;
        }
        delete zz;
        return false;
    }
}

bool Counter::conputerCounter(Plan plan){
    struct tms start, end;
    times(&start);
    
    // for(int i=0;i<counterset.size();i++){
    //     cout<<i<<"次"<<endl;
    //     counterset[i]->dump();
    // }
    smt="";cout<<222<<endl;
    /*转换初始状态为SMT公式*/
    initToSmt();
    
    addActionToGoal(plan);
    addRestraintToTime0();
    for(set<string>::iterator iter=variables.begin(); iter!=variables.end(); iter++){
        // set<string> variable = counter->getVariables();
	// for(set<string>::iterator var=variable.begin();var!=variable.end();var++)
		smt+="(declare-const ";
        smt+=*iter;
        smt+=" Bool)\n";
        // cout<<"(declare-const "<<*iter<<" Bool)"<<endl;
	// std::cout << __cplusplus << std::endl;
    }
    smt+=init_smt;
    // cout<<init_smt<<endl;
    smt+=regret_smt;
    // cout<<regret_smt<<endl;
    smt+=sasrestraint_smt;
    // cout<<sasrestraint_smt<<endl;
    // cout<<smt<<endl;
    /*调用z3求解器求反例，并且进行提取*/
    int isvaliplan = false;
    isvaliplan = invokeZ3();
    clearAll();
    times(&end);
    int total_ms = (end.tms_utime - start.tms_utime) * 10;
    total_counter+=total_ms;
    return isvaliplan;
    
}




void Counter::testPlanisvalid(Plan plan){   
    vector<int> var_tmp = g_original_values;
    vector<pair<int,int>> tmp;
    vector<state_var> curStates;
    int plansize = plan.size();
    int var_len = g_initial_state->vars.size();
    /*识别其中每个状态都相同的fact*/
    int *isunKnownFact = (int*)calloc(var_len,sizeof(int));
    memset(isunKnownFact,0,var_len);
    /*先识别or中的*/
    for(int i=0;i<oneofs.orlens;i++){
        int nowindex=0;
        /*识别or中的*/
        for(int j=0;j<oneofs.oneof[i].len;j++){
            for(int k=0;k<oneofs.oneof[i].size[j];k++){
                isunKnownFact[oneofs.oneof[i].var[nowindex]]=1;
                g_initial_state->negate_var(oneofs.oneof[i].var[nowindex]);
                nowindex++;
            }
        }
    }
    /*再识别oneof中的*/
    for(int i=0;i<oneofs.lens;i++){
        int nowindex=0;
        int index = oneofs.orlens+i;
        /*识别or中的*/
        for(int j=0;j<oneofs.oneof[index].len;j++){
            for(int k=0;k<oneofs.oneof[index].size[j];k++){
                isunKnownFact[oneofs.oneof[index].var[nowindex]]=1;
                g_initial_state->negate_var(oneofs.oneof[index].var[nowindex]);
                nowindex++;
            }
        }
    }

    /*识别*/
    for(int i=0;i<var_len;i++){
        if(isunKnownFact[i]){
            var_tmp[i]=g_variable_domain[i]-1;
        }
    }

    ifstream infile;
    infile.open("belief", ios::in);
    string line;
    while(getline(infile, line)){
        // cout<<line<<endl;
        if(line == "END_BELIEF"){
            state_var newvar;
            newvar.vars = var_tmp;
            newvar.frequency=0;
            curStates.push_back(newvar);
            for(int i=0;i<tmp.size();i++){
                var_tmp[tmp[i].first] = g_variable_domain[tmp[i].first]-1;
            }
            tmp.clear();
        }else{
            int var,val;
            var = -1;		
            for(int i = 0 ; i < g_variable_name.size() ; i++)
            {
                /*读取的name后面有一个空格，长度会+1*/
                if(line.find(g_variable_name[i]) == 0 && line.size() == g_variable_name[i].size()+1)
                {
                    var = i;
                    // cout << g_variable_name[i]<<" ";
                }
            }
            getline(infile, line);
            stringstream ss(line);
            ss >> val;
            // cout<<var<<" "<<val<<endl;
            var_tmp[var]=val;
            tmp.push_back(pair<int,int>(var,val));
        }
    }
    infile.close();
    // cout<<curStates.size()<<endl;
    // cout<<endl;
    // for(int i=0;i<curStates.size();i++){
    //     cout<<"第"<<i<<"个状态"<<endl;
    //     for(int j=0;j<curStates[i].vars.size();j++){
    //         if(isunKnownFact[j]&&curStates[i].vars[j]!=g_variable_domain[j]-1)
    //             cout<<g_variable_name[j]<<"-"<<curStates[i].vars[j]<<" ";
    //     }
    //     cout<<endl;
    // }


    for(int i=0;i<plansize;i++){
         /*所有的状态后移*/
        // cout<<plan[i]->get_name()<<":"<<endl;
        for(int j=0;j<curStates.size();j++){
            int h;
            for(h=0;h<g_operators.size();h++)
            {
                if(g_operators[h].get_name().compare(plan[i]->get_name()) == 0) break;
            }
            applyAction(&curStates[j],g_operators[h]);
        }
    }

    cout<<endl;
    /*再对目标状态运用axiom*/
    for(int k=0;k<curStates.size();k++){
        for(auto ot : axiomtovar){
            bool issatisfy=false;
            /*如果满足其中一个，那么就会break出来*/
            for(int i=0;i<ot.second.size();i++){
                // cout<<"(-["<<ot.second[i].var<<","<<ot.second[i].pre<<"]-";
                if(curStates[k].vars[ot.second[i].var]!=ot.second[i].pre)
                    continue;
                int acess_num=0;
                for(int j=0;j<ot.second[i].cond.size();j++){
                    // cout<<"["<<ot.second[i].cond[j].var<<","<<ot.second[i].cond[j].prev<<"]-";
                    if(curStates[k].vars[ot.second[i].cond[j].var]==ot.second[i].cond[j].prev)
                        acess_num++;
                    
                }
                if(acess_num==ot.second[i].cond.size()){
                    issatisfy=true;
                    break;
                }
                // cout<<")"<<endl;
            }
            // cout<<"issatisfy:"<<issatisfy<<endl;
            if(issatisfy)
                curStates[k].vars[ot.first.first] = ot.first.second;
            // cout<<"->["<<ot.first.first<<"-"<<ot.first.second<<"]"<<endl;
        }
    }
    
    // cout<<endl;
    // cout<<"后"<<endl;
    // for(int i=0;i<curStates.size();i++){
    //     cout<<"第"<<i<<"个状态"<<endl;
    //     for(int j=0;j<curStates[i].vars.size();j++){
    //         if(isunKnownFact[j]&&curStates[i].vars[j]!=g_variable_domain[j]-1)
    //             cout<<g_variable_name[j]<<"-"<<curStates[i].vars[j]<<" ";
    //     }
    //     cout<<endl;
    // }
    /*遍历curstate_验证是否为有效解*/
    int isvalidplan=true;
    for(int i=0;i<curStates.size();i++){
        for(int j=0;j<g_goal.size();j++){
            /*test*/
            // cout<<"当前对比:"<<curStates[i].vars[g_goal[j].first]<<"与"<<g_goal[j].second<<endl;
            if(curStates[i].vars[g_goal[j].first]!=g_goal[j].second){
                isvalidplan=false;
                cout<<"状态"<<i<<"不能解决"<<endl;
                for(int k=0;k<curStates[i].vars.size();k++){
                    cout<<g_variable_name[k]<<"-"<<curStates[i].vars[k]<<" ";
                }
                cout<<endl;
                break;
            }
                
        }

    }
    if(isvalidplan){
        cout<<"规划解能解反例集！"<<endl;
        counterissolvered=true;
    }else{
        cout<<"规划解还不能解反例集！"<<endl;
        counterissolvered=false;
    }

}