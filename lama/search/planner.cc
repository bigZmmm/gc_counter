/*********************************************************************
 * Author: Malte Helmert (helmert@informatik.uni-freiburg.de)
 * (C) Copyright 2003-2004 Malte Helmert
 * Modified by: Silvia Richter (silvia.richter@nicta.com.au),
 *              Matthias Westphal (westpham@informatik.uni-freiburg.de)             
 * (C) Copyright 2008 NICTA and Matthias Westphal
 *
 * This file is part of LAMA.
 *
 * LAMA is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 3
 * of the license, or (at your option) any later version.
 *
 * LAMA is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, see <http://www.gnu.org/licenses/>.
 *
 *********************************************************************/

#include "best_first_search.h"
#include "wa_star_search.h"
#include "ff_heuristic.h"
#include "globals.h"
#include "operator.h"
#include "landmarks_graph.h"
#include "landmarks_graph_rpg_sasp.h"
#include "landmarks_count_heuristic.h"
#include "counter.h"

#include <memory>
#include <cassert>
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <sys/times.h>
#include <climits>
#include <string.h>


using namespace std;

vector<std::pair<int, int>> g_goal_tmp;
void show_action();
bool solve_belief_state(BestFirstSearchEngine* engine);
bool solve_belief_state_ite(BestFirstSearchEngine* subengine);
int save_plan(const vector<const Operator *> &plan, const string& filename, int iteration);


BestFirstSearchEngine *search_subplan(State *init_state, vector<pair<int, int> > subgoal, bool ff_heuristic, bool ff_preferred_operators);

void print_heuristics_used(bool ff_heuristic, bool ff_preferred_operators, 
			   bool landmarks_heuristic, 
			   bool landmarks_heuristic_preferred_operators);

BestFirstSearchEngine *search_subplan(State *init_state, bool ff_heuristic, bool ff_preferred_operators);

string stateToStringmain(state_var s){
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
int operateTimes=0;

int main(int argc, const char **argv) {
    struct tms start, search_start, search_end, end;
    struct tms landmarks_generation_start, landmarks_generation_end;
    times(&start);
    bool poly_time_method = false;
    string plan_filename = "sas_plan";
    
    bool ff_heuristic = false, ff_preferred_operators = false;
    bool landmarks_heuristic = false, landmarks_preferred_operators = false;
    bool reasonable_orders = true;
    bool iterative_search = false;
    g_display = false;
    enum {wa_star, bfs} search_type = bfs;
    /*默认ff_heuristic=true,默认ff_preferred_operators = true*/
	if(argc < 2 || argc > 4) {
	std::cout << "Usage: \"search options [outputfile]\"\n";
    }
    else {
		for(const char *c = argv[1]; *c != 0; c++) {
			if(*c == 'f') {
			/*默认开启*/
			ff_heuristic = true;
			} else if(*c == 'F') {
			/*默认开启*/
			ff_preferred_operators = true;
			} else if(*c == 'l') {
					landmarks_heuristic = true; 
			} else if(*c == 'L') {
					landmarks_preferred_operators = true; 
			} else if(*c == 'w') {
					search_type = wa_star;
			} else if(*c == 'i') {
					iterative_search = true;
			} else {
				cerr << "Unknown option: " << *c << endl;
				return 1;
			}
		}
		if(argc >= 3)
		{
			plan_filename = argv[2];
			if(strcmp(argv[3],"true")==0) g_display = true;
		}
    }
    if(!ff_heuristic && !landmarks_heuristic) {
	cerr << "Error: you must select at least one heuristic!" << endl
	     << "If you are unsure, choose options \"fFlL\"." << endl;
	return 2;
    }
    cin >> poly_time_method;
    if(poly_time_method) {
	cout << "Poly-time method not implemented in this branch." << endl;
	cout << "Starting normal solver." << endl;
    }

    // Read input and generate landmarks
    bool generate_landmarks = false;
    g_lgraph = NULL; 
    g_lm_heur = NULL;
    /*无*/
	if(landmarks_heuristic || landmarks_preferred_operators) 
		generate_landmarks = true;
    
	/*landmarks_generation_start时间*/
	times(&landmarks_generation_start);
    
	/*将output中的数据全部读入到类中*/
	read_everything(cin, generate_landmarks, reasonable_orders);
    // dump_everything();

    times(&landmarks_generation_end);
    int landmarks_generation_ms = (landmarks_generation_end.tms_utime - 
				   landmarks_generation_start.tms_utime) * 10;
    /*无*/
	if(g_lgraph != NULL) {
	cout << "Landmarks generation time: " << landmarks_generation_ms / 1000.0 
	     << " seconds" << endl;
    }

    // Check whether landmarks were found, if not switch to FF-heuristic.
    if(generate_landmarks && g_lgraph->number_of_landmarks() == 0) {
		cout << "No landmarks found. This should only happen if task is unsolvable." << endl;

		/*无*/
		if(landmarks_heuristic) {
			cout << "Disabling landmarks count heuristic." << endl;
			landmarks_heuristic = false;
		}

		/*有*/
		if(!ff_heuristic) {
			cout << "Using FF heuristic with preferred operators." << endl;
			ff_heuristic = true;
			ff_preferred_operators = true;
		}
    }

    int iteration_no = 0;
    bool solution_found = false;
	/*暂时不知道什么意思*/
    int wa_star_weights[] = {10, 5, 3, 2, 1, -1};
    int wastar_bound = -1;
    g_ff_heur = NULL;
    int wastar_weight = wa_star_weights[0];
    bool reducing_weight = true;
	
	/*这个循环只会一次，相当于没有*/
    do{
		iteration_no++;
		cout << "Search iteration " << iteration_no << endl;
		// 未使用迭代搜索
		if(reducing_weight && wa_star_weights[iteration_no - 1] != -1)
			wastar_weight = wa_star_weights[iteration_no - 1];
		else {
			cout << "No more new weight, weight is " << wastar_weight << endl;
			reducing_weight = false;
		}
		// Initialize search engine and heuristics (this is cheap and we want to vary search type
		// and heuristics, so we initialize freshly in each iteration)
		/*这里只使用到了bfs，不再迭代使用多种搜索方式*/
		BestFirstSearchEngine* engine; 
		//addin
		g_ff_heur = new FFHeuristic;
		
			// no prefer operator
	   	// open_lists.push_back(OpenListInfo(g_ff_heur, false));

		if(search_type == wa_star)
			// Parameters of WAStar are 1) weight for heuristic, 2) upper bound on solution
			// cost (this cuts of search branches if the cost of a node exceeds the bound), 
			// use -1 for none.
			engine = new WAStarSearchEngine(wastar_weight, wastar_bound);  
		/*默认bfs，gclama并没有改变*/
		
		print_heuristics_used(ff_heuristic, ff_preferred_operators, 
					landmarks_heuristic, landmarks_preferred_operators);
		/*不会再使用*/
		if(landmarks_heuristic || landmarks_preferred_operators) {
		/*
			if(landmarks_preferred_operators)
			if(!g_ff_heur)
				g_ff_heur = new FFHeuristic;
			g_lm_heur = new LandmarksCountHeuristic(
			*g_lgraph, *engine, landmarks_preferred_operators, g_ff_heur);
			engine->add_heuristic(g_lm_heur, landmarks_heuristic,
					landmarks_preferred_operators);
		*/
		}
		
		// Search
		int plan_cost = INT_MAX;
		bool ctask;
		//times(&search_start);
		/*不断对第一个状态进行求解，ctask为false时，一直循环*/
		// for(int i=0;i<g_variable_domain.size();i++){
		// 	cout<<i<<"-"<<g_variable_domain[i]<<endl;
		// }
		
		g_initial_state->dump();

		/*这里要调用一次反例求解，得到一个初始状态*/
		vector<const Operator *> Plan;
		counter = new Counter();
		g_goal_tmp = g_goal;
		// cout<<"当前目标的大小"<<g_goal.size()<<endl;
		// counter->selectMinState();
		// cout<<"当前目标的大小"<<g_goal.size()<<endl;
		// counter->conputerCounter(Plan,true);

		/*根据这个来选择初始状态*/
		if(counter->oneofs.type==2)
			counter->selectLandmark();
		else
			counter->conputerCounter(Plan,true);
		
		/*用于保存第一个反例*/
		state_var firststate;
		firststate.frequency=1;
		firststate.vars=g_initial_state->vars;
		string firststatestring = stateToStringmain(firststate);
		state_var initial_state;
		initial_state.vars = g_initial_state->vars;
		
		if(counter->oneofs.type==2){
			counter->appearcounter.insert(pair<string,state_var>(firststatestring,firststate));
			counter->counterset_new.push_back(firststate);
		}
		

		/*已经作为s0的进行禁止*/
		counter->firststate.insert(pair<string,state_var>(stateToStringmain(initial_state),initial_state));
		
		/*根据第一个反例进行搜索*/
		engine = new BestFirstSearchEngine;
		if(ff_heuristic || ff_preferred_operators) {
		//	    if(!g_ff_heur)
		//		g_ff_heur = new FFHeuristic;
			/*修改了*/
			engine->add_heuristic( ff_heuristic,
					ff_preferred_operators);
		}

		fail_time=0;
		do {
			/*这个和里面的不一样?里面能解决,这里不能解?*/
			g_initial_state->dump();
			engine->search();
			operateTimes++;
			//times(&search_end);
			if(engine->found_solution())
			{
				/*输出s0状态*/
				// g_initial_state->dump();
				/*plan_filename表示输入时需要保存信息的位置*/
				cout<<engine->get_plan().size()<<endl;
				plan_cost = save_plan(engine->get_plan(), plan_filename, iteration_no);
				
				g_initial_state->vars = firststate.vars;
				counter->appearcounter.insert(pair<string,state_var>(firststatestring,firststate));
				counter->counterset_new.push_back(firststate);
			}else{

				/*无解说明当前反例作为初始状态不可行，切换初始状态，并把这一个在初始状态中禁止*/
				cout<<"一开始就没有解！？"<<endl;
				cout<<"no validplan found!"<<endl;
				if(!counter->conputerCounter(Plan,true)){
					cout<<"该规划器不能解该问题！"<<endl;
					break;
				}
				// g_initial_state->dump();
				
				/*已经作为s0的进行禁止*/
				state_var loop_initial_state;
				loop_initial_state.vars = g_initial_state->vars;
				counter->firststate.insert(pair<string,state_var>(stateToStringmain(loop_initial_state),loop_initial_state));

				/*更新s0*/
				firststate = counter->counterset_new[0];
				firststatestring = stateToStringmain(firststate);
				cout<<"firststate:"<<counter->firststate.size()<<endl;
				engine = search_subplan(g_initial_state,g_goal,true,true);
				
			}
			
			cout<<"plansize:"<<engine->get_plan().size()<<endl;
			// ctask = true;
			ctask = solve_belief_state_ite(engine);
			if (!ctask){
				cout << "reach dead end!" << endl;
				fail_time++;
				/*上一个解搜索失败，清空反例集*/
				counter->appearcounter.clear();
				counter->counterset_new.clear();
			}
		}
		while (!ctask);

		times(&end);
		int total_ms = (end.tms_utime - start.tms_utime) * 10;
		cout << "Total time: " << total_ms / 1000.0 << " seconds" << endl;

		/*engine->statistics();
		int search_ms = (search_end.tms_utime - search_start.tms_utime) * 10;
		cout << "Search time: " << search_ms / 1000.0 << " seconds" << endl;
		int total_ms = (search_end.tms_utime - start.tms_utime) * 10;
		cout << "Total time: " << total_ms / 1000.0 << " seconds" << endl;*/
		
		solution_found |= engine->found_solution();
		/*没有找到解，退出循环*/
		if(!engine->found_solution())
			iterative_search = false;

		// Set new parameters for next search
		search_type = wa_star;
		wastar_bound = plan_cost;
		if(wastar_weight <= 2) { // make search less greedy
			ff_preferred_operators = false;
			landmarks_preferred_operators = false;
		}

		// If the heuristic weight was already 0, we can only search for better solutions
		// by decreasing the bound (note: this could be improved by making WA* expand 
		// all fringe states, but seems to have little importance).
		if(wastar_weight == 0) {
			wastar_bound--;
		}

    }
    while(iterative_search);

    return solution_found ? 0 : 1; 
}
void show_action()
{
	for(int i=0;i<g_operators.size();i++)
		g_operators[i].dump();
}

void printPlan(vector<const Operator *> plan){
	cout<<"规划长度："<<plan.size()<<endl;
    for(int i=0;i<plan.size();i++){
        cout<<plan[i]->get_name()<<" ";
    }
    cout<<endl;
}

bool sovle_counter(vector<const Operator *> oldplan){
	 State* current_state;
     State* previous_state;
     State* check_plan_state;
     vector<const Operator *> plan;
     vector<const Operator *> subplan;
     bool maintain_maximum = true;
     BestFirstSearchEngine *subsubengine;
//     cout << "Initial " << endl;
//     g_initial_state->dump();
     int iter = 0;
     int iteration = 0;
	 int belief_size = 0;
     int last_modified = 0;
     bool valid_plan = false;
    //  int operateTimes=1;
	 /*将s0的plan插入*/
     subplan.insert(subplan.end(),oldplan.begin(),oldplan.end());

	 /*将当前状态赋值为初始状态*/
     current_state = new State(); 
     current_state->assign(*g_initial_state);
	 /*前一个状态也赋值为初始状态*/
	 previous_state = new State();
    //  previous_state->assign(*g_initial_state);
     /*这个也是初始状态*/
	 check_plan_state = new State();
     check_plan_state->assign(*g_initial_state);
	 plan.clear();
	 plan.insert(plan.end(),subplan.begin(),subplan.end());
	 for(map<string,state_var>::iterator t=counter->appearcounter.begin();t!=counter->appearcounter.end();t++){
		/*只处理被约束的状态*/
		if(t->second.frequency<2)
			continue;
		check_plan_state->vars=t->second.vars;
		/*检查该状态是否能到达目标状态*/
		for(int i=0;i<plan.size();i++)
		{ 
			/*找到操作下标*/
			int j;
			for(j=0;j<g_operators.size();j++)
			{
				if(g_operators[j].get_name().compare(plan[i]->get_name()) == 0) break;
			}
			/*操作可用，check_plan_state后移*/
			if(g_operators[j].is_applicable(*check_plan_state))
			{
				check_plan_state->assign(State(*check_plan_state,g_operators[j]));
						//cout << "current state" << endl;
							//check_plan_state->dump();
			}
		}
		/*检查该状态是否达到目标*/
		
		if(check_plan_state->satisfy_subgoal(g_goal))
		{
			cout<<"issatisfy:1"<<endl;
			continue;
		}
		cout<<"issatisfy:0"<<endl;
		
		previous_state->assign(*g_initial_state);
		current_state->vars=t->second.vars;		
		//plan.insert(plan.end(),subsubengine->get_plan().begin(),subsubengine->get_plan().end());
		/*plan使得该状态不能到达目标状态 | plan中有动作不适用*/
		int i=0;
		/*之前的plan，不适用当前状态，在当前状态中进行插入*/
		while(i<plan.size())
		{
			/*找到当前的opera下标*/
			int j;
			for(j=0;j<g_operators.size();j++)
			{
				if(g_operators[j].get_name().compare(plan[i]->get_name()) == 0) break;
			}
			/*如果前置条件和条件影响是相同的变量，则两个都检查，否则只需要检查前置条件*/
			/*满足前置条件或者即满足前置条件，又满足条件影响*/
			/**/
			// cout<<i<<"是否满足:"<<g_operators[j].is_conformant_applicable(*current_state)<<endl;
			if(g_operators[j].is_conformant_applicable(*current_state))
			{
				vector<pair <int, int> > sub_goal;
				vector<const Operator *> sub_plan;					
				/*前一个状态在该plan下的条件影响 */
				sub_goal = g_operators[j].condition_sub_goal(*previous_state);
				
				/*如果有一个的条件影响是不满足的，那么后面的都不再进行子目标的求解*/
				/*？？？？*/
				// if(maintain_maximum == false) sub_goal.clear();				
				// cout<<!current_state->satisfy_subgoal(sub_goal)<<endl;
				/*当前状态不满足这个子目标*/
				if(counter->unapplyaction==0)
				if(!current_state->satisfy_subgoal(sub_goal))
				{
					/*找到这个子规划*/
					subsubengine = search_subplan(current_state,sub_goal,true,true);
					operateTimes++;
					//cout << "subsub 1 " << endl;
					/*插入到第i个动作前*/
					if(subsubengine->found_solution())
					{
						sub_plan = subsubengine->get_plan();
						/*insert(a,b,c)  将b-c插入到a位置*/
						plan.insert(plan.begin()+i,subsubengine->get_plan().begin(),subsubengine->get_plan().end());
						// cout<<"2.plan"<<endl;
						// printPlan(plan);
						/*当前状态后移*/
						for(int k=0;k<sub_plan.size();k++)
						{
							/*下标k*/
							int h;
							for(h=0;h<g_operators.size();h++)
							{
								if(g_operators[h].get_name().compare(sub_plan[k]->get_name()) == 0) break;
							}
							if(g_display)
							{
								g_operators[h].dump();
							}
							current_state->assign(State(*current_state, g_operators[h]));
						}
						i=i+subsubengine->get_plan().size();
					}
					/*下面不满足是直接退出？*/
					else
					{
						cout<<"没有找到！"<<endl;
						// maintain_maximum = false;
					}
					delete subsubengine;
				} 	
				/*当前状态和后续状态都后移*/
				current_state->assign(State(*current_state, g_operators[j]));
				previous_state->assign(State(*previous_state, g_operators[j]));
				
				// current_state->dump();
				i++;
			}
			/*不满足前置条件*/
			else
			{
				//cout << "not applicable";
				//g_operators[j].dump();
				vector<pair <int, int> > sub_goal;
				/*当前状态不满足的前置条件和条件影响*/
				sub_goal = g_operators[j].conformant_sub_goal(*current_state);
				vector<const Operator *> sub_plan;					
				subsubengine = search_subplan(current_state,sub_goal,true,true);
				operateTimes++;
				//cout << " subsub 2" << endl;
				if (!subsubengine->found_solution())
				{
					cout<<plan.size()<<endl;
					plan.erase(plan.begin()+i);
					cout<<plan.size()<<endl;
					continue;
				}
				sub_plan = subsubengine->get_plan();
				/*将子plan插入第i个动作前*/
				plan.insert(plan.begin()+i,subsubengine->get_plan().begin(),subsubengine->get_plan().end());
				// cout<<"3.plan"<<endl;
				// printPlan(sub_plan);
				/*将当前状态后移*/
				for(int k=0;k<sub_plan.size();k++)
				{
					int h;
					for(h=0;h<g_operators.size();h++)
					{
						if(g_operators[h].get_name().compare(sub_plan[k]->get_name()) == 0) break;
					}
					if(g_display)
					{
						g_operators[h].dump();
					}
					current_state->assign(State(*current_state, g_operators[h]));
				}
				current_state->assign(State(*current_state, g_operators[j]));
				i=i+subsubengine->get_plan().size()+1;
				delete subsubengine;

			}
		}
		/*当前状态*/
		// cout<<"当前状态"<<endl;
		// current_state->dump();
		/*再找一遍，查看经过上面的操作后，最终能否到达目标状态*/
		subsubengine = search_subplan(current_state,g_goal,true,true);
		operateTimes++;
		if (!subsubengine->found_solution())
		{
			return false;
		}
		subplan.clear();
		
		/*将新形成的plan与之前的plan连接*/
		subplan.insert(subplan.end(),subsubengine->get_plan().begin(),subsubengine->get_plan().end());
		plan.insert(plan.end(),subplan.begin(),subplan.end());
		// cout<<"4.plan"<<endl;
		// printPlan(subplan);
		/*此状态前满足的状态*/
		g_initial_state->vars=t->second.vars;
		delete subsubengine;
	}
	counter->newplan.insert(counter->newplan.end(),plan.begin(),plan.end());


	return true;
}

bool havecounterfrequencycout1(){
	bool flag = false;
	for(map<string,state_var>::iterator t=counter->appearcounter.begin();t!=counter->appearcounter.end();t++){
		if(t->second.frequency>5){
			return true;
		}
	}
	return flag;
}

/*修改的迭代版本*/
bool solve_belief_state_ite(BestFirstSearchEngine* subengine){
	int qiehuan = 0;
    State* current_state;
    State* previous_state;
    State* check_plan_state;
    vector<const Operator *> plan;
    vector<const Operator *> subplan;
    bool maintain_maximum = true;
    BestFirstSearchEngine *subsubengine;
	set<string> action_notreach;
    int iter = 0;
    int iteration = 0;
	int belief_size = 0;
    int last_modified = 0;
    bool valid_plan = false;
	
	/*将s0的plan插入*/
    subplan.insert(subplan.end(),subengine->get_plan().begin(),subengine->get_plan().end());
	 
	/*将当前状态赋值为初始状态*/
    current_state = new State(); 
    current_state->assign(*g_initial_state);
	previous_state = new State();
    previous_state->assign(*g_initial_state);
	check_plan_state = new State();
    check_plan_state->assign(*g_initial_state);
	//  printPlan(subplan);
	int yinxian1=0,yinxian2=0,test1=0;
	 
	plan.clear();
	for(;;){
		iteration++;
		cout<<"第"<<iteration<<"次迭代"<<endl;
		
		plan.insert(plan.end(),subplan.begin(),subplan.end());
		subplan.clear();
		// cout<<"规划长度:"<<plan.size()<<endl;
		printPlan(plan);
		
		/*对当前的规划解进行化简，只有能找到反例才化简，不能找到反例只有两种情况(此时均已对初始状态约束放开)：1、前一次有约束时无反例，并且对这些约束进行了求解 2、前一次无约束时无反例*/
		if(!counter->isfind){
			counter->optimizePlantest(plan);
			plan.clear();
			plan.insert(plan.end(),counter->newplan.begin(),counter->newplan.end());
			counter->newplan.clear();
		}else{
			counter->counterissolvered=true;
		}
		
		// counter->counterissolvered=true;

		// cout<<"1.plan"<<endl;
		// printPlan(plan);
		
		/*两种选择参考方式的方法*/
		if(counter->findfinallandmark){
			string prestatestring = "";
			for(int i=0;i<previous_state->vars.size();i++){
				if(previous_state->vars[i]!=(g_variable_domain[i]-1)){
					prestatestring+=to_string(i);
					prestatestring+="-";
					prestatestring+=to_string(previous_state->vars[i]);
					prestatestring+='.';
				}
			}
			if(counter->appearcounter.find(prestatestring)!= counter->appearcounter.end()&&counter->appearcounter[prestatestring].frequency>1){
				qiehuan=1;
				for(map<string,state_var>::iterator t=counter->appearcounter.begin();t!=counter->appearcounter.end();t++){
					if(t->second.frequency==1){
						previous_state->vars=t->second.vars;
						check_plan_state->vars = t->second.vars;
						break;
					}
				}
			}else
				previous_state->assign(*check_plan_state);
		}else{
			previous_state->assign(*g_initial_state);
		}
		
		// 

		if(!counter->conputerCounter(plan,false)){
			if(!counter->counterissolvered){
				cout<<"还不是最终解，对反例中不能解的状态继续求解"<<endl;
				bool sovle = sovle_counter(plan);
				plan.clear();
				plan.insert(plan.end(),counter->newplan.begin(),counter->newplan.end());
				
				// counter->counterissolvered=true;
				counter->newplan.clear();
				continue;
			}
			else{
				// if(valid_plan==false){
				// 	cout<<"切换子目标为最终目标"<<endl;
				// 	g_goal = g_goal_tmp;
				// 	subsubengine = search_subplan(current_state,g_goal,true,true);
				// 	printPlan(subsubengine->get_plan());
				// 	plan.insert(plan.end(),subsubengine->get_plan().begin(),subsubengine->get_plan().end());
				// 	printPlan(plan);
				// 	delete subsubengine;
				// 	valid_plan=true;
				// 	continue;
				// }
				valid_plan=true;
				break;
			}
		}
		
		// 退出这一次求解的条件，重复在一个状态中循环，不可解状态
		if(havecounterfrequencycout1()){
			cout<<"重复在一个状态中循环！！！"<<endl;
			return false;
		}

		/*current_state更新为g_initial_state*/
		current_state->assign(*g_initial_state);
		cout << "Initial State:" << endl;
		for(int v=0;v<g_initial_state->vars.size();v++){
			if(g_initial_state->vars[v]!=g_variable_domain[v]-1)
				cout << "  " << g_variable_name[v] << ": " << g_initial_state->vars[v] << endl;
		}
		cout << "Previou State:" << endl;
		for(int v=0;v<previous_state->vars.size();v++){
			if(previous_state->vars[v]!=g_variable_domain[v]-1)
				cout << "  " << g_variable_name[v] << ": " << previous_state->vars[v] << endl;
		}
    	
		last_modified = 0;
		//plan.insert(plan.end(),subsubengine->get_plan().begin(),subsubengine->get_plan().end());
		/*plan使得该状态不能到达目标状态 | plan中有动作不适用*/
		int i=0;
		/*之前的plan，不适用当前状态，在当前状态中进行插入*/
		/**/
		// maintain_maximum=false;
		while(i<plan.size())
		{
			/*找到当前的opera下标*/
			int j;
			for(j=0;j<g_operators.size();j++)
			{
				if(g_operators[j].get_name().compare(plan[i]->get_name()) == 0) break;
			}

			/*如果前置条件和条件影响是相同的变量，则两个都检查，否则只需要检查前置条件*/
			/*满足前置条件或者即满足前置条件，又满足条件影响*/
			
			/*修改只需要满足前置条件，不要考虑条件影响*/
			// cout<<i<<"是否满足:"<<g_operators[j].is_conformant_applicable(*current_state)<<endl;
			if(g_operators[j].is_conformant_applicable(*current_state))
			{
				vector<pair <int, int> > sub_goal;
				vector<const Operator *> sub_plan;					
				
				/*617待修改，这里可能前面的状态也不满足*/
				/*前一个状态在该plan下的条件影响 */
				/*包括前置条件和条件影响*/

				/*原：仅仅考虑条件影响变量数小于等于1的*/
				/*改为贪婪的考虑所有的条件影响变量*/
				sub_goal = g_operators[j].condition_sub_goal(*previous_state);
				// cout<<i<<" "<<g_operators[j].get_name()<<": 2.sub_goal:"<<sub_goal.size()<<endl;
				
				/*原：如果有一个的条件影响是不满足的，那么后面的都不再进行子目标的求解*/
				/*修改：如果有一个的条件影响不满足，后面的也要进行子目标的求解*/
				if(maintain_maximum == false) sub_goal.clear();	
				
				//add
				// if(action_notreach.find(g_operators[j].get_name())!=action_notreach.end()){
				// 	test1++;
				// 	sub_goal.clear();	
				// } 
				/*test*/
				// cout<<"当前的action_notreach"<<endl;
				// for (auto it = action_notreach.begin(); it != action_notreach.end(); ++it)
				// 	cout << *it << endl;
				// cout<<g_operators[j].get_name()<<endl;
				// cout<<!current_state->satisfy_subgoal(sub_goal)<<endl;
				
				/*当前状态不满足这个子目标*/
				// if(counter->unapplyaction==0)
				if(!current_state->satisfy_subgoal(sub_goal))
				{
					if(g_display)
					{
						cout << "fail to execute action:" << endl;
						g_operators[j].dump();
						cout << "need to maintain effect:" << endl;
							for(int d = 0; d < sub_goal.size(); d++)
								cout << "  " << g_variable_name[sub_goal[d].first] << ": "
								<< sub_goal[d].second << endl;
					}

					/*找到这个子规划*/
					subsubengine = search_subplan(current_state,sub_goal,true,true);
					operateTimes++;
					//cout << "subsub 1 " << endl;
					/*插入到第i个动作前*/
					
					if(subsubengine->found_solution())
					{
						sub_plan = subsubengine->get_plan();
						plan.insert(plan.begin()+i,subsubengine->get_plan().begin(),subsubengine->get_plan().end());
						cout<<i<<": 2.plan"<<endl;
						printPlan(subsubengine->get_plan());
						//判断是否会影响到其他动作

						if(g_display)
						{
							cout << "insert the following actions into plan--confor:" << endl;
						}
						/*当前状态后移*/
						for(int k=0;k<sub_plan.size();k++)
						{
							/*下标k*/
							int h;
							for(h=0;h<g_operators.size();h++)
							{
								if(g_operators[h].get_name().compare(sub_plan[k]->get_name()) == 0) break;
							}
							if(g_display)
							{
								g_operators[h].dump();
							}
							current_state->assign(State(*current_state, g_operators[h]));
						}
						i=i+subsubengine->get_plan().size();
					}
					/*下面不满足是直接退出？*/
					else
					{
						cout<<i<<" 没有找到！"<<endl;
						yinxian1++;
						//add
						// action_notreach.insert(g_operators[j].get_name());
						// maintain_maximum = false;
					}
					
					delete subsubengine;
				}
				// cout << "apply ";
				// g_operators[j].dump();		
				// current_state->dump();		
				/*当前状态和后续状态都后移?是否要同样保证前置条件符合*/

				/*原：无论如何都会移动*/
				/*修改：只有满足才移动，否则会出现前面满足，但到这个地方不满足。这里本不回出现问题，但由于参考状态的选择，可能导致这种情况*/
				if(g_operators[j].is_conformant_applicable(*current_state)&&g_operators[j].is_conformant_applicable(*previous_state)){
					current_state->assign(State(*current_state, g_operators[j]));
					previous_state->assign(State(*previous_state, g_operators[j]));
				}else{
					cout<<"不能移动"<<endl;
				}
					
				// if(g_operators[j].is_conformant_applicable(*previous_state))
				// current_state->dump();
				i++;
			}
			/*不满足前置条件，或者前置条件中有一样的，不满足前置条件和条件影响*/
			else
			{
				// cout << "not applicable";
				//g_operators[j].dump();
				vector<pair <int, int> > sub_goal;
				/*当前状态不满足的前置条件和条件影响*/
				sub_goal = g_operators[j].conformant_sub_goal(*current_state);
				if(g_display)
				{
					g_operators[j].dump();
					cout << "need to maintain minimum effect:" << endl;
						for(int d = 0; d < sub_goal.size(); d++)
							cout << "  " << g_variable_name[sub_goal[d].first] << ": "
							<< sub_goal[d].second << endl;
				}
				vector<const Operator *> sub_plan;					
				subsubengine = search_subplan(current_state,sub_goal,true,true);
				operateTimes++;
				
				/*原：如果有不满足的直接舍弃该plan*/
				/*修改：不舍弃，仅删除不满足前置条件的动作。因为有删除操作，能够寻找最大的可解度，尽可能寻找质量更好的解*/
				if (!subsubengine->found_solution())
				{
					if(g_display) 
					{
						cout << "No plan was found. Backtracking." << endl;
					}
					// return false;
					cout<<i<<":"<<plan[i]->get_name()<<"前置条件不满足"<<endl;
					yinxian2++;
					plan.erase(plan.begin()+i);
					continue;
				}
				sub_plan = subsubengine->get_plan();
				/*将子plan插入第i个动作前*/
				plan.insert(plan.begin()+i,subsubengine->get_plan().begin(),subsubengine->get_plan().end());
				cout<<i<<": 3.plan"<<endl;
				printPlan(sub_plan);
				if(g_display)
				{
					cout << "insert the following actions into plan:" << endl;
				}
				/*添加将当前状态后移*/
				for(int k=0;k<sub_plan.size();k++)
				{
					int h;
					for(h=0;h<g_operators.size();h++)
					{
						if(g_operators[h].get_name().compare(sub_plan[k]->get_name()) == 0) break;
					}
					if(g_display)
					{
						g_operators[h].dump();
					}
					current_state->assign(State(*current_state, g_operators[h]));
				}
				current_state->assign(State(*current_state, g_operators[j]));
				i=i+subsubengine->get_plan().size()+1;
				delete subsubengine;

			}
			// cout<<i<<endl;
			// current_state->dump();
		}
		if(g_display)
		{
			cout << "check if we need to insert actions after the plan to satisfy goal" << endl;
		}
		/*当前状态*/
		// cout<<"经过规划解后的当前状态"<<endl;
		// current_state->dump();
		/*再找一遍，查看经过上面的操作后，最终能否到达目标状态*/
		subsubengine = search_subplan(current_state,g_goal,true,true);
		operateTimes++;
		if (!subsubengine->found_solution())
		{
			if(g_display) 
			{
				cout << "No plan was found. Backtracking." << endl;
			}
			return false;
		}
		
		/*将新形成的plan与之前的plan连接*/
		subplan.insert(subplan.end(),subsubengine->get_plan().begin(),subsubengine->get_plan().end());
		cout<<"4.plan"<<endl;
		printPlan(subplan);
		
		/*添加：此状态作为切换子目标为总目标时的当前状态*/
		for(int k=0;k<subplan.size();k++)
		{
			int h;
			for(h=0;h<g_operators.size();h++)
			{
				if(g_operators[h].get_name().compare(subplan[k]->get_name()) == 0) break;
			}
			if(g_display)
			{
				g_operators[h].dump();
			}
			current_state->assign(State(*current_state, g_operators[h]));
		}
		if(g_display)
		{
			if(subsubengine->get_plan().size()==0)
			{	
				cout << "Valid plan. No need to insert more action" << endl;
			}
			else
			{
				cout << "Insert the following actions into plan:" << endl;
				for(int k=0;k<subsubengine->get_plan().size();k++)
				{
					int h;
					for(h=0;h<g_operators.size();h++)
					{
						if(g_operators[h].get_name().compare(subsubengine->get_plan()[k]->get_name()) == 0) break;
					}
					g_operators[h].dump();
				}
			}
		}
		delete subsubengine;
	}
	/*迭代完成后，判断反例集合是否能解决，如果有未完成的，还要对这一部分进行求解*/

	// plan.insert(plan.end(),subplan.begin(),subplan.end());
	subplan.clear();
	if(!valid_plan) return false;
    ofstream outfile;
    outfile.open("finalplan", ios::out);
    for(int k=0;k<plan.size();k++)
    {
		// cout << plan[k]->get_name() << endl;
		outfile << plan[k]->get_name() << endl;
    }
    outfile.close();     
	// counter->optimizePlan(plan);
	// counter->optimizePlantest(plan);
	// counter->conputerCounter(plan,false);
	// counter->optimizePlan(counter->newplan);
	int k=0;
	for(map<string,state_var>::iterator t=counter->appearcounter.begin();t!=counter->appearcounter.end();t++){
		// cout<<"状态"<<k<<"出现在反例集中的次数："<<t->second.frequency<<endl;
		if(t->second.frequency>1)
			k++; 
	}
	counter->testPlanisvalid(plan);
	// cout<<"test1:"<<test1<<endl;
	cout<<"是否找到landmark:"<<counter->findfinallandmark<<endl;
	cout<<"切换"<<qiehuan<<endl;
	cout<<"影响1:"<<yinxian1<<endl;
	cout<<"影响2:"<<yinxian2<<endl;
	cout<<"删除不满足前置条件的动作数:"<<counter->unapplyaction<<endl;
	cout<<"最终反例集大小:"<<counter->appearcounter.size()<<endl;
	cout<<"反例集中出现次数大于1的反例数:"<<k<<endl;
	cout<<"检测到可精简plan次数:"<<counter->sum<<endl;
	cout<<"belief_size:"<<counter->getBelief_size()<<endl;
	cout<<"operate size:"<<operateTimes<<endl;
	cout<<"final plan: plan_size "<<plan.size()<< endl;
	cout<<"iteration:"<<iteration<<endl;
	cout<<"fail_time:"<<fail_time<<endl;
	cout<<"landmark time:"<<counter->landmarktime /1000.0 <<endl;
	cout<<"counter time:"<<counter->getTotal_counter()/ 1000.0 << " seconds" << endl;

	//ofstream outfile;       
	outfile.open("C_Plan", ios::out);
	int numberofactions = 0;
	for(int i=0;i<plan.size();i++)
	{
		int h;
		for(h=0;h<g_operators.size();h++)
		{
			if(g_operators[h].get_name().compare(plan[i]->get_name()) == 0) break;
		}
		if (g_operators[h].index_number ==-1)
		{
			g_operators[h].index_number = numberofactions;
			numberofactions++;
		}
	}
	outfile << "0" << endl;
	outfile << "%%" <<endl;
	outfile << numberofactions << " ";
	int action_count = 0;
	for(int i=0;i<plan.size();i++)
	{
		int h;
		for(h=0;h<g_operators.size();h++)
		{
			if(g_operators[h].get_name().compare(plan[i]->get_name()) == 0) break;
		}
		if (g_operators[h].index_number >=action_count) 
		{
			outfile << "(" << g_operators[h].get_name() << ") ";
			action_count++;
		}
	}
	outfile << endl;
	outfile << "%%" <<endl;
	outfile << "linear " << plan.size() << " ";
	for(int i=0;i<plan.size();i++)
	{
		int h;
		for(h=0;h<g_operators.size();h++)
		{
			if(g_operators[h].get_name().compare(plan[i]->get_name()) == 0) break;
		}
		outfile << g_operators[h].index_number << " ";
	}
	outfile.close();
	return true;	
}


/*subengine：求解s0的求解器，原版本*/
bool solve_belief_state(BestFirstSearchEngine* subengine)
{
     //show_action();
     cout << "Open belief states" << endl;
     ifstream infile;

     std::string name;
	 /*var：对应g_variable_name下标,val：该变量的值*/
     vector<pair<int,int> > prev_values;
     vector<pair<int,int> > new_values;
     State* current_state;
     State* previous_state;
     State* check_plan_state;
     vector<const Operator *> plan;
     vector<const Operator *> subplan;
     bool first = true;
     bool maintain_maximum = true;
     BestFirstSearchEngine *subsubengine;

//     cout << "Initial " << endl;
//     g_initial_state->dump();

     int iter = 0;
     int belief_size = 0;
     int last_modified = 0;
     bool valid_plan = false;
	 
	 /*将s0的plan插入*/
     subplan.insert(subplan.end(),subengine->get_plan().begin(),subengine->get_plan().end());

	 /*将当前状态赋值为初始状态*/
     current_state = new State(); 
     current_state->assign(*g_initial_state);
	 /*前一个状态也赋值为初始状态*/
	 previous_state = new State();
     previous_state->assign(*g_initial_state);
     /*这个也是初始状态*/
	 check_plan_state = new State();
     check_plan_state->assign(*g_initial_state);
     int operateTimes=1;
	 do 
     {
		cout << "iteration " << iter << endl;
		
		/*读取belief文件中所有的初始状态*/
		infile.open("belief", ios::in);
		int bstate =0;     
		
		/*新的开始*/
		subplan.insert(subplan.end(),plan.begin(),plan.end());
		plan.clear();
		
		/*遍历belief中的每一个状态*/
		/*修改：改变这里每次循环，不再是读取belief，而是每次反例添加后，再对这个反例插入，并且再用的plan验证所有的反例，最后调用一次SMT求解器*/
		while(getline(infile, name))
		{
			// 已经读取完一个状态
			

			if(name == "END_BELIEF") {
				/*每次循环都要调用一次*/
				
				
				/*如果是第一次，不搜索*/
				if(first)
				{
					// cout << "Initial State:" << endl;
    				// g_initial_state->dump();
					belief_size++;
					//cout << "first time, no search" << endl;
					first = false;
					/*赋予prev刚刚读取的状态*/
					prev_values = new_values;
					//restore values when there is axiom
					
					/*初始化g_initial_state*/
					g_initial_state->vars = g_original_values;
					//restore values when there is axiom
					for(int i=0;i<prev_values.size();i++)
					{
						g_initial_state->negate_var(prev_values[i].first);
					}
					new_values = vector<pair<int, int> > ();
					
				}
				else
				{
					// cout << "Initial State:" << endl;
   					//  g_initial_state->dump();
					/*第0次循环就要一直增加belief_size的大小*/
					if(iter==0) belief_size++;
					/*last_modified == belief_size，确定plan满足belief_size个状态，退出，*/
					
					/*第iter==0时不可能，因为有一个不满足就会赋予last_modified=0*/
					/*用于后两次循环*/
					if(last_modified == belief_size)
					{
						valid_plan = true;
						break;
					}
					/*保存s0状态的所有变量赋值*/
					g_original_values = g_initial_state->vars;
					/*设置为当前状态，用于规划器求解*/
					current_state->assign(*g_initial_state);
					if(g_display)
					{
						current_state->dump();
					}
					plan.insert(plan.end(),subplan.begin(),subplan.end());

					//check plan
					bool fill_in = false; //是否之前的规划满足当前状态 this variable determines if the previous plan satisfies current initial state
					/*赋值为当前状态，检查是否之前的plan满足当前状态*/
					check_plan_state->assign(*g_initial_state);
					if(g_display)
					{
						cout << "check if previous plan satisfies current initial state " << endl;
								//cout << "current state" << endl;
								//check_plan_state->dump();
					}
					/*检查之前的plan是否满足现在的
						改用SMT，这一步没必要，因为当前这个初始状态肯定是不满足的*/
					for(int i=0;i<plan.size();i++)
					{ 
						/*找到操作下标*/
						int j;
						for(j=0;j<g_operators.size();j++)
						{
							if(g_operators[j].get_name().compare(plan[i]->get_name()) == 0) break;
						}
						/*操作可用，check_plan_state后移*/
						if(g_operators[j].is_applicable(*check_plan_state))
						{
							check_plan_state->assign(State(*check_plan_state,g_operators[j]));
									//cout << "current state" << endl;
										//check_plan_state->dump();
						}
						/*不可用*/
						else
						{
							if(g_display)
							{
								cout << "No. Fail at:" << endl;
								g_operators[j].dump();
							}
							fill_in = true;
							break;
						}
					}
					/*plan所有动作都适用*/
					if(fill_in == false)
					{
						/*到达的状态包含目标状态，转而对下一个状态处理，last_modified++*/
						if(check_plan_state->satisfy_subgoal(g_goal))
						{
							/*满足的状态值+1*/
							last_modified++;
							if(g_display)
							{
										/*cout << "final state:" << endl;
										check_plan_state->dump();
										dump_goal();*/
								cout << "previous plan satisfies current initial state " << endl;
							}
							/*状态已经满足，previous_state赋值为当前状态，进入下一次循环*/
							previous_state->assign(*g_initial_state);
							prev_values = new_values;
							/*初始化g_initial_state*/
							for(int i=0;i<prev_values.size();i++)
							{
								g_initial_state->negate_var(prev_values[i].first);
							}
							new_values = vector<pair<int, int> > ();
							subplan.clear();
							continue;
						}
					}
					//check plan

					/**/
					last_modified = 0;
					//plan.insert(plan.end(),subsubengine->get_plan().begin(),subsubengine->get_plan().end());
					
					/*plan使得该状态不能到达目标状态 | plan中有动作不适用*/
					int i=0;
					/*之前的plan，不适用当前状态，在当前状态中进行插入*/
					/**/
					while(i<plan.size())
					{
						/*找到当前的opera下标*/
						int j;
						for(j=0;j<g_operators.size();j++)
						{
							if(g_operators[j].get_name().compare(plan[i]->get_name()) == 0) break;
						}

						/*如果前置条件和条件影响是相同的变量，则两个都检查，否则只需要检查前置条件*/
						/*满足前置条件或者即满足前置条件，又满足条件影响*/
						if(g_operators[j].is_conformant_applicable(*current_state))
						{
							vector<pair <int, int> > sub_goal;
							vector<const Operator *> sub_plan;					
							/*前一个状态在该plan下的条件影响 */
							sub_goal = g_operators[j].condition_sub_goal(*previous_state);
							
							/*如果有一个的条件影响是不满足的，那么后面的都不再进行子目标的求解*/
							/*？？？？*/
							if(maintain_maximum == false) sub_goal.clear();				
							
							/*当前状态不满足这个子目标*/
							if(!current_state->satisfy_subgoal(sub_goal))
							{
								if(g_display)
								{
									cout << "fail to execute action:" << endl;
									g_operators[j].dump();
									cout << "need to maintain effect:" << endl;
										for(int d = 0; d < sub_goal.size(); d++)
											cout << "  " << g_variable_name[sub_goal[d].first] << ": "
											<< sub_goal[d].second << endl;
								}

								/*找到这个子规划*/
								subsubengine = search_subplan(current_state,sub_goal,true,true);
								operateTimes++;
								//cout << "subsub 1 " << endl;
								/*插入到第i个动作前*/
								if(subsubengine->found_solution())
								{
									sub_plan = subsubengine->get_plan();
									/*insert(a,b,c)  将b-c插入到a位置*/
									plan.insert(plan.begin()+i,subsubengine->get_plan().begin(),subsubengine->get_plan().end());
									if(g_display)
									{
										cout << "insert the following actions into plan--confor:" << endl;
									}
									/*当前状态后移*/
									for(int k=0;k<sub_plan.size();k++)
									{
										/*下标k*/
										int h;
										for(h=0;h<g_operators.size();h++)
										{
											if(g_operators[h].get_name().compare(sub_plan[k]->get_name()) == 0) break;
										}
										if(g_display)
										{
											g_operators[h].dump();
										}
										current_state->assign(State(*current_state, g_operators[h]));
									}
									i=i+subsubengine->get_plan().size();
								}
								/*下面不满足是直接退出？*/
								else
								{
									cout<<"没有找到！"<<endl;
									// maintain_maximum = false;
								}
								
								delete subsubengine;
							} 
							//cout << "apply ";
							//g_operators[j].dump();				
							/*当前状态和后续状态都后移*/
							current_state->assign(State(*current_state, g_operators[j]));
							previous_state->assign(State(*previous_state, g_operators[j]));
							//current_state->dump();
							i++;
						}
						/*不满足前置条件*/
						else
						{
							//cout << "not applicable";
							//g_operators[j].dump();
							vector<pair <int, int> > sub_goal;
							/*当前状态不满足的前置条件和条件影响*/
							sub_goal = g_operators[j].conformant_sub_goal(*current_state);
							if(g_display)
							{
								g_operators[j].dump();
								cout << "need to maintain minimum effect:" << endl;
									for(int d = 0; d < sub_goal.size(); d++)
										cout << "  " << g_variable_name[sub_goal[d].first] << ": "
										<< sub_goal[d].second << endl;
							}
							vector<const Operator *> sub_plan;					
							subsubengine = search_subplan(current_state,sub_goal,true,true);
							operateTimes++;
							//cout << " subsub 2" << endl;
							if (!subsubengine->found_solution())
							{
								if(g_display) 
								{
									cout << "No plan was found. Backtracking." << endl;
								}
								i++;
								continue;
								// return false;
							}
							sub_plan = subsubengine->get_plan();
							/*将子plan插入第i个动作前*/
							plan.insert(plan.begin()+i,subsubengine->get_plan().begin(),subsubengine->get_plan().end());
							if(g_display)
							{
								cout << "insert the following actions into plan:" << endl;
							}
							/*将当前状态后移*/
							for(int k=0;k<sub_plan.size();k++)
							{
								int h;
								for(h=0;h<g_operators.size();h++)
								{
									if(g_operators[h].get_name().compare(sub_plan[k]->get_name()) == 0) break;
								}
								if(g_display)
								{
									g_operators[h].dump();
								}
								current_state->assign(State(*current_state, g_operators[h]));
							}
							current_state->assign(State(*current_state, g_operators[j]));
							i=i+subsubengine->get_plan().size()+1;
							
							delete subsubengine;

						}
					}
					if(g_display)
					{
						cout << "check if we need to insert actions after the plan to satisfy goal" << endl;
					}

					/*再找一遍，查看经过上面的操作后，最终能否到达目标状态*/
					subsubengine = search_subplan(current_state,g_goal,true,true);
					operateTimes++;
					if (!subsubengine->found_solution())
					{
						if(g_display) 
						{
							cout << "No plan was found. Backtracking." << endl;
						}
						return false;
					}
					prev_values = new_values;
					
					/*初始化*/
					//restore values
					g_initial_state->vars = g_original_values;
					//restore values
					for(int i=0;i<prev_values.size();i++)
					{
						g_initial_state->negate_var(prev_values[i].first);
					}
					new_values = vector<pair<int, int> > ();
					subplan.clear();
					
					/*将新形成的plan与之前的plan连接*/
					subplan.insert(subplan.end(),subsubengine->get_plan().begin(),subsubengine->get_plan().end());
					/*此状态前满足的状态*/
					
					if(g_display)
					{
						if(subsubengine->get_plan().size()==0)
						{	
							cout << "Valid plan. No need to insert more action" << endl;
						}
						else
						{
							cout << "Insert the following actions into plan:" << endl;
							for(int k=0;k<subsubengine->get_plan().size();k++)
							{
								int h;
								for(h=0;h<g_operators.size();h++)
								{
									if(g_operators[h].get_name().compare(subsubengine->get_plan()[k]->get_name()) == 0) break;
								}
								g_operators[h].dump();
							}
						}
					}
					delete subsubengine;
				}
				
			}
			/*还没有将一个完整的状态读入*/
			/*修改：不需要读取，只需要把这个当成反例输入，变成新的初始状态
			  var是变量的下标 val是变量的值
			*/
			else
			{
				/*修改：学习这个对初始状态进行插入*/
				int var,val;
				var = -1;		
					
				for(int i = 0 ; i < g_variable_name.size() ; i++)
				{
					/*读取的name后面有一个空格，长度会+1*/
					if(name.find(g_variable_name[i]) == 0 && name.size() == g_variable_name[i].size()+1)
					{
						var = i;
						// cout << g_variable_name[i]<<" ";
					}
				}
				getline(infile, name);
				stringstream ss(name);
				ss >> val;
				// cout << val << endl;
				if (var!=-1) {
					g_initial_state->set_var(var,val);
					/*var：对应g_variable_name下标,val：该变量的值*/
					new_values.push_back(make_pair(var,val));
				}
			}
		}
		plan.insert(plan.end(),subplan.begin(),subplan.end());

		subplan.clear();
		infile.close();
		iter++;
    }
    while(iter < 3);
	// Counter *counter = new Counter;
	// counter->conputerCounter(plan);
	
	if(!valid_plan) return false;
    ofstream outfile;
    outfile.open("finalplan", ios::out);
    for(int k=0;k<plan.size();k++)
    {
		cout << plan[k]->get_name() << endl;
		outfile << plan[k]->get_name() << endl;
    }
     outfile.close();     
		cout<<"belief_size:"<<belief_size<<endl;
	cout<<"operate size:"<<operateTimes<<endl;
	cout << "final plan: plan_size "<<plan.size()<< endl;
	//ofstream outfile;       
	outfile.open("C_Plan", ios::out);
	int numberofactions = 0;
	for(int i=0;i<plan.size();i++)
	{
		int h;
		for(h=0;h<g_operators.size();h++)
		{
			if(g_operators[h].get_name().compare(plan[i]->get_name()) == 0) break;
		}
		if (g_operators[h].index_number ==-1)
		{
			g_operators[h].index_number = numberofactions;
			numberofactions++;
		}
	}
	outfile << "0" << endl;
	outfile << "%%" <<endl;
	outfile << numberofactions << " ";
	int action_count = 0;
	for(int i=0;i<plan.size();i++)
	{
		int h;
		for(h=0;h<g_operators.size();h++)
		{
			if(g_operators[h].get_name().compare(plan[i]->get_name()) == 0) break;
		}
		if (g_operators[h].index_number >=action_count) 
		{
			outfile << "(" << g_operators[h].get_name() << ") ";
			action_count++;
		}
	}
	outfile << endl;
	outfile << "%%" <<endl;
	outfile << "linear " << plan.size() << " ";
	for(int i=0;i<plan.size();i++)
	{
		int h;
		for(h=0;h<g_operators.size();h++)
		{
			if(g_operators[h].get_name().compare(plan[i]->get_name()) == 0) break;
		}
		outfile << g_operators[h].index_number << " ";
	}
	outfile.close();
	return true;	
}



int save_plan(const vector<const Operator *> &plan, const string& filename, int iteration) {
    ofstream outfile;
    int plan_cost = 0;
    bool separate_outfiles = true; // IPC conditions, change to false for a single outfile.
    cout<<"g_use_metric:"<<g_use_metric<<endl;
	if(separate_outfiles) {
		// Write a separat output file for each plan found by iterative search
		stringstream it_no;
		it_no << iteration;
		outfile.open((filename + "." + it_no.str()).c_str(), ios::out);
    }
    else {
		// Write newest plan always to same output file
		outfile.open(filename.c_str(), ios::out);
    }
    for(int i = 0; i < plan.size(); i++) {
		int action_cost =  plan[i]->get_cost();
		/*metric是什么*/
		if(g_use_metric)
			action_cost--; // Note: action costs have all been increased by 1 to deal with 0-cost actions
		plan_cost += action_cost;
		if(!g_use_metric)
			cout << plan[i]->get_name() << endl;
		else
			cout << plan[i]->get_name() << " (" 
			<< action_cost << ")" << endl;
		outfile << "(" << plan[i]->get_name() << ")" << endl;
    }
    outfile.close();
    if(!g_use_metric)
		cout << "Plan length: " << plan.size() << " step(s)." << endl;
    else 
		cout << "Plan length: " << plan.size() << " step(s), cost: " 
	     << plan_cost << "." << endl;
    return plan_cost;
}

void print_heuristics_used(bool ff_heuristic, bool ff_preferred_operators, 
			   bool landmarks_heuristic, 
			   bool landmarks_preferred_operators) {
    cout << "Using the following heuristic(s):" << endl;
    if(ff_heuristic) {
		cout << "FF heuristic ";
		if(ff_preferred_operators)
			cout << "with preferred operators";
		cout << endl;
    }
    if(landmarks_heuristic) {
	cout << "Landmark heuristic ";
	if(landmarks_preferred_operators)
	    cout << "with preferred operators";
	cout << endl;
    }
}

BestFirstSearchEngine *search_subplan(State *init_state, vector<pair<int, int> > subgoal, bool ff_heuristic, bool ff_preferred_operators) {
    
    //initialize subint & subgoal
    State* temp;
    temp = g_initial_state;
    g_initial_state = init_state;
    vector<pair<int, int> > tmpgoal;
    
    tmpgoal.insert(tmpgoal.end(),g_goal.begin(),g_goal.end());
    g_goal.clear();
    g_goal.insert(g_goal.begin(),subgoal.begin(),subgoal.end());

    BestFirstSearchEngine *subengine;
    subengine = new BestFirstSearchEngine;
	/*再启动一次搜索*/
    subengine->add_heuristic(ff_heuristic, ff_preferred_operators);
    subengine->search();

    g_initial_state = temp;
    g_goal.clear();
    g_goal.insert(g_goal.begin(),tmpgoal.begin(),tmpgoal.end());

    
    return subengine;
}


