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

Counter::Counter(){
    struct tms start, end;
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
    cout<<"axiom"<<endl;
    for(auto ot : axiomtovar){
        for(int i=0;i<ot.second.size();i++){
            // cout<<"(-["<<ot.second[i].var<<","<<ot.second[i].pre<<"]-";
            for(int j=0;j<ot.second[i].cond.size();j++){
                // cout<<"["<<ot.second[i].cond[j].var<<","<<ot.second[i].cond[j].prev<<"]-";
            }
            // cout<<")"<<endl;
        }
        // cout<<"->["<<ot.first.first<<"-"<<ot.first.second<<"]"<<endl;
    }
    // for(int i = 0 ; i < g_variable_name.size() ; i++){
    //     cout<<indextovar[i]<<" "<<i<<endl;
    // }
    times(&end);
    int total_ms = (end.tms_utime - start.tms_utime) * 10;
    total_counter+=total_ms;
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
                if(oneofs.oneof[i].var[nowindex]!=oneofs.oneof[i].var[nowindex-oneofs.oneof[i].size[j-1]]){
                    is1var=false;
                    break;
                }
                nowindex+=oneofs.oneof[i].size[j];
            }
            
            /*所有状态对应的SMT*/
            vector<string> all_state;
            /*构建oneof的SMT*/
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
    for(int i=0;i<prepost.size();i++){
        if(a->isadd(now_facts.first,now_facts.second,i)){
            if(prepost[i].cond.size()>1)
                    add_smt+="(and ";
            if(prepost[i].cond.size()>0)
            for(int j=0;j<prepost[i].cond.size();j++){
                string vari = varToSmt(prepost[i].cond[j].var,prepost[i].cond[j].prev,time_step-1);
                variables.insert(vari);
                add_smt+= vari;
                add_smt+=" ";
                new_facts->insert(pair<int,int>(prepost[i].cond[j].var,prepost[i].cond[j].prev));
            }
            else{
                add_smt+= "true";
                add_smt+=" ";
            }
            if(prepost[i].cond.size()>1)
                add_smt+=") ";
        }
        if(a->isdel(now_facts.first,now_facts.second,i)){
            if(prepost[i].cond.size()>1)
                    notdel_smt+="(and ";
            if(prepost[i].cond.size()>0)
            for(int j=0;j<prepost[i].cond.size();j++){
                string vari = varToSmt(prepost[i].cond[j].var,prepost[i].cond[j].prev,time_step-1);
                variables.insert(vari);
                notdel_smt+= vari;
                notdel_smt+=" ";
                new_facts->insert(pair<int,int>(prepost[i].cond[j].var,prepost[i].cond[j].prev));
            }
            else{
                notdel_smt+= "true";
                notdel_smt+=" ";
            }
            if(prepost[i].cond.size()>1)
                notdel_smt+=") ";
        }
    }
    add_smt+=")";
    notdel_smt+="))";
    // cout<<"add:"<<add_smt<<" del:"<<notdel_smt<<endl<<endl;
    /*提取回归的前置条件*/
    // for(int i=0;i<prevail.size();i++){
    //     string vari = varToSmt(prevail[i].var,prevail[i].prev,time_step-1);
    //     // preference_var->insert(vari);
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
        cout<<now_fact.first<<" "<<now_fact.second<<endl;
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

    cout<<"规划长度："<<plan.size()<<endl;
    for(int i=0;i<plan.size();i++){
        cout<<plan[i]->get_name()<<" ";
    }
    cout<<endl;
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

bool Counter::conputerCounter(Plan plan){
    struct tms start, end;
    times(&start);
    smt="";
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
    /*调用z3求解器求反例，并且进行提取*/
    map<int,int> sample;
    Z3_counter *zz = new Z3_counter();
    bool isFind = zz->extracCounter(smt,&sample);
    delete zz;
    // cout<<"修改前："<<endl;
    // for(int i = 0 ; i < g_variable_name.size() ; i++){
    //     cout<<g_variable_name[i]<<" "<<g_initial_state->vars[i]<<endl;
    // }
    cout<<isFind<<endl;
    times(&end);
    int total_ms = (end.tms_utime - start.tms_utime) * 10;
    total_counter+=total_ms;
    if(isFind){
        for(int i=0;i<g_initial_state->vars.size();i++){
          int var = indextovar[i];
          if(sample.find(var)!=sample.end())
              g_initial_state->set_var(i,sample[var]);
        }
        // cout<<"修改后："<<endl;
        // for(int i = 0 ; i < g_variable_name.size() ; i++){
        //     cout<<g_variable_name[i]<<" "<<g_initial_state->vars[i]<<endl;
        // }  
        clearAll();
        return true;
    }else{
        clearAll();
        return false;
    }
    
}