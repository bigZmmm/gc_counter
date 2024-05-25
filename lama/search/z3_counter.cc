#include "z3_counter.h"
#include <string>
#include <map>
#include <utility>
bool Z3_counter::extracCounter(std::string smt,std::map<int,int> *sample) {
    context c;
    solver s(c);
    s.add(c.parse_string(smt.c_str()));
    // std::cout<<s<<"\n";
    // std::cout << s.check() << "\n";
    // std::cout << s.check() << "\n";
    /*0:unsat 1:sat 2:unknown*/
    int issat = s.check();
    if(issat==1){
        std::cout<<"找到反例！"<<std::endl;
        model m = s.get_model();
        /*n为所有的变量数*/
        int n=m.num_consts();
        std::cout<<"SMT变量数:"<<n<<std::endl;
        /*读取变量名以及变量的真值*/
        for(int i=0;i<n;i++){
            func_decl cnst = m.get_const_decl(i);
            expr istrue = m.get_const_interp(cnst);
            std::string name = cnst.name().str();
            /*表示为真的值*/
            if(istrue.bool_value()==1){
                int var=0,val=0,timestep=0,j=0,namesize=name.size();
                while(name[j]!='-'){
                    if(name[j]>=48&&name[j]<=57){
                        var*=10;
                        var+=(name[j]-48);
                    }
                    j++;
                }
                j++;
                while(name[j]!='-'){
                    if(name[j]>=48&&name[j]<=57){
                        val*=10;
                        val+=(name[j]-48);
                    }
                    j++;
                }
                j++;
                while(j<=namesize){
                    if(name[j]>=48&&name[j]<=57){
                        timestep*=10;
                        timestep+=(name[j]-48);
                    }
                    j++;
                }
                if(timestep==0){
                    sample->insert(std::pair<int,int>(var,val));
                }
                // std::cout<<var<<" "<<val<<" "<<timestep<<std::endl;
            }
            // std::cout<<name<<" "<<istrue.bool_value()<<std::endl;
        }
        // std::cout<<m.to_string()<<std::endl;
        return true;
    }else if(issat==0){
        std::cout<<"没有反例，找到最终解！"<<std::endl;
        return false;
    }else if(issat==1){
        std::cout<<"unknown!!"<<std::endl;
        return false;
    }
    
    // std::cout << "Model:\n" << m << "\n";
    // std::cout << "x*y = " << m.eval(x*y) << "\n";
}