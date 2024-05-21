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
    /*读取oneof进入*/
    ifstream infile;
    infile.open("oneof", ios::in);
    string line;
    /*读取类型*/
    getline(infile, line);
    if(line=="ORS")
        oneofs.type=true;
    else 
        oneofs.type=false;
    /*读取数量*/
    getline(infile, line);
    istringstream ss(line);
    ss >> oneofs.lens;
    for(int i=0;i<oneofs.lens;i++){
        oneof_item tmp;
        tmp.len=0;
        oneofs.oneof.push_back(tmp);
    }
    int index=0,andsize=0,prevar=-1;
    while(getline(infile, line)){
        if(line==", "){
            oneofs.oneof[index].size.push_back(andsize);
            andsize=0;
        }
        if(line=="END_ONEOF"||(line==", "&&oneofs.type==true)){
            oneofs.oneof[index].len = oneofs.oneof[index].size.size();
            index++;
        }
        else if(line!=", "){
            andsize++;
            int var,val;
            if(line=="NULL"){
                var = prevar;
                val = g_variable_domain[var]-1;
                if (var!=-1) {
                    /*var：对应g_variable_name下标,val：该变量的值*/
                    oneofs.oneof[index].var.push_back(var);
                    oneofs.oneof[index].val.push_back(val);
                }
            }
            else{
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
                if (var!=-1) {
                    /*var：对应g_variable_name下标,val：该变量的值*/
                    oneofs.oneof[index].var.push_back(var);
                    oneofs.oneof[index].val.push_back(val);
                }
                prevar=var;
            }
            
        }
    }
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
    // for(int i = 0 ; i < g_variable_name.size() ; i++){
    //     cout<<indextovar[i]<<" "<<i<<endl;
    // }

}
void Counter::initToSmt(){
    init_smt="(assert (and\n";
    /*1.转换初始状态的SMT公式，并且记录所有的变量*/
    // dump_everything();
    int var_len = g_initial_state->vars.size();
    /*识别其中每个状态都相同的fact*/
    int *isunKnownFact = (int*)calloc(var_len,sizeof(int));
    memset(isunKnownFact,0,var_len);
    /*多种状态的oneof*/
    if(oneofs.type){
        /*第一次循环，识别known_fact*/
        for(int i=0;i<oneofs.lens;i++){
            int nowindex=0;
            for(int j=0;j<oneofs.oneof[i].len;j++){
                for(int k=0;k<oneofs.oneof[i].size[j];k++){
                    isunKnownFact[oneofs.oneof[i].var[nowindex]]=1;
                    nowindex++;
                }
            }
        }
        int state_size=0;
        /*添加known_fact*/
        for(int i=0;i<var_len;i++){
            if(isunKnownFact[i]==0){
                string var0 = varToSmt(i,g_initial_state->vars[i],0);
                variables.insert(var0);
                init_smt+=" ";
                init_smt+=var0;
                init_smt+="\n";
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
        /*第一次循环，识别known_fact*/
        for(int i=0;i<oneofs.lens;i++){
            int nowindex=0;
            for(int j=0;j<oneofs.oneof[i].len;j++){
                for(int k=0;k<oneofs.oneof[i].size[j];k++){
                    isunKnownFact[oneofs.oneof[i].var[nowindex]]=1;
                    nowindex++;
                }
            }
        }
        int state_size=0;
        /*添加known_fact*/
        for(int i=0;i<var_len;i++){
            if(isunKnownFact[i]==0){
                string var0 = varToSmt(i,g_initial_state->vars[i],0);
                variables.insert(var0);
                cout<<var0<<endl;
                init_smt+=" ";
                init_smt+=var0;
                init_smt+="\n";
            }else{
                state_size++;
            }
        }
        /*遍历所有的oneof,生存oneof的smt代码*/
        for(int i=0;i<oneofs.lens;i++){
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
                if(!is1var){
                    tmp+="(and ";
                    nowindex=0;
                    for(int k=0;k<oneofs.oneof[i].len;k++){
                        for(int m=0;m<oneofs.oneof[i].size[k];m++){
                            string var0="";
                            if(k==j){
                                var0+=varToSmt(oneofs.oneof[i].var[nowindex],oneofs.oneof[i].val[nowindex],0);
                            }else{
                                var0+=varToSmt(oneofs.oneof[i].var[nowindex],g_variable_domain[oneofs.oneof[i].var[nowindex]]-1,0);
                            }
                            nowindex++;
                            variables.insert(var0);
                            tmp+=var0;
                            tmp+=" ";
                        }
                    }
                    tmp+=")";
                }
                else if(is1var)
                    for(int m=0;m<oneofs.oneof[i].size[j];m++){
                        string var0="";
                        var0+=varToSmt(oneofs.oneof[i].var[nowindex],oneofs.oneof[i].val[nowindex],0);
                        nowindex++;
                        variables.insert(var0);
                        tmp+=var0;
                        tmp+=" ";
                    }
                first_or+=tmp;
                first_or+=" ";
                all_state.push_back(tmp);
            }
            first_or+=")";
            // cout<<first_or<<endl;
            init_smt+=first_or;
            init_smt+="\n";
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
    for(int i=0;i<prevail.size();i++){
        string vari = varToSmt(prevail[i].var,prevail[i].prev,time_step-1);
        preference_var->insert(vari);
        variables.insert(vari);
        new_facts->insert(pair<int,int>(prevail[i].var,prevail[i].prev));
    }
    
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
    int plan_size = plan.size();
    /*添加目标状态*/
    for(int i = 0; i < g_goal.size(); i++){
        string var_goal = varToSmt(g_goal[i].first,g_goal[i].second,plan_size);
        preference_var.insert(var_goal);
        variables.insert(var_goal);
        now_facts.insert(pair<int, int>(g_goal[i].first, g_goal[i].second));
    }
    /*从目标状态开始进行回归*/
    for(int i=plan_size-1;i>=0;i--){
        set< pair<int,int> > new_facts;
        for(set<pair<int, int> >::iterator iter=now_facts.begin(); iter!=now_facts.end(); iter++){
            regretCurFact(plan[i],&preference_var,pair<int,int>(iter->first,iter->second),&new_facts,i+1);
        }
        now_facts.clear();
        now_facts=new_facts;
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