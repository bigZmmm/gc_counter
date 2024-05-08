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

void show_action();
bool solve_belief_state(BestFirstSearchEngine* engine);
int save_plan(const vector<const Operator *> &plan, const string& filename, int iteration);


BestFirstSearchEngine *search_subplan(State *init_state, vector<pair<int, int> > subgoal, bool ff_heuristic, bool ff_preferred_operators);

void print_heuristics_used(bool ff_heuristic, bool ff_preferred_operators, 
			   bool landmarks_heuristic, 
			   bool landmarks_heuristic_preferred_operators);

BestFirstSearchEngine *search_subplan(State *init_state, bool ff_heuristic, bool ff_preferred_operators);
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
/*
    cout << "goal" << endl;
    for(int x=0;x<g_goal.size();x++)
    {
		cout << g_variable_name[g_goal[x].first] << " " << g_goal[x].second << endl;
    }
	for(int i=0;i<g_operators.size();i++)
    {
        g_operators[i].dump();
    }
    for(int i=0;i<g_axioms.size();i++)
    {
        g_axioms[i].dump();
    }
*/
	/*这个循环只会一次，相当于没有*/
    do{
		iteration_no++;
		cout << "Search iteration " << iteration_no << endl;
		// wa_star_weights[iteration_no - 1] != -1 表示迭代iteration_no=6
		if(reducing_weight && wa_star_weights[iteration_no - 1] != -1)
			// 如果 iteration_no！=6
			wastar_weight = wa_star_weights[iteration_no - 1];
		else {
			//iteration_no=6后，关闭，此时wastar_weight=1
			cout << "No more new weight, weight is " << wastar_weight << endl;
			reducing_weight = false;
		}
		// Initialize search engine and heuristics (this is cheap and we want to vary search type
		// and heuristics, so we initialize freshly in each iteration)
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
		/*默认这个，gclama并没有改变*/
		else
			engine = new BestFirstSearchEngine;

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
		if(ff_heuristic || ff_preferred_operators) {
		//	    if(!g_ff_heur)
		//		g_ff_heur = new FFHeuristic;
			/*修改了*/
			engine->add_heuristic( ff_heuristic,
					ff_preferred_operators);
		} 

		// Search
		int plan_cost = INT_MAX;
		bool ctask;
		//times(&search_start);
		/*不断对第一个状态进行求解，ctask为false时，一直循环*/
		do {
			engine->search();
			//times(&search_end);
			
			if(engine->found_solution())
			{
				/*输出s0状态*/
				g_initial_state->dump();
				/*plan_filename表示输入时需要保存信息的位置*/
				plan_cost = save_plan(engine->get_plan(), plan_filename, iteration_no);
			}
			/*为true说明找到了解，不用再遍历后面的解了*/
			ctask = solve_belief_state(engine);
			if (!ctask)
				cout << "reach dead end!" << endl;
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


bool solve_belief_state(BestFirstSearchEngine* subengine)
{
     //show_action();
     cout << "Open belief states" << endl;
     ifstream infile;

     std::string name;
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
     
	 do 
     {
		cout << "iteration " << iter << endl;
		/*belief所有的初始状态*/
		infile.open("belief", ios::in);
		int bstate =0;     
		
		subplan.insert(subplan.end(),plan.begin(),plan.end());
		plan.clear();     
		/*遍历每一个确定性的初始状态*/
		/*修改：这里每次循环，不再是每次读取belief，而是每次反例添加后，再对这个反例插入，并且再用的plan验证所有的反例，最后调用一次SMT求解器*/
		while(getline(infile, name))
		{
			// 已经读取完一个状态
			
			if(name == "END_BELIEF") {
				cout<<endl;
				/*如果是第一次，不搜索*/
				if(first)
				{
					belief_size++;
					//cout << "first time, no search" << endl;
					first = false;
					prev_values = new_values;
					//restore values when there is axiom
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
					if(iter==0) belief_size++;
					/*确定该plan满足所有的状态，退出*/
					if(last_modified == belief_size)
					{
						valid_plan = true;
						break;
					}
					/*?*/
					g_original_values = g_initial_state->vars;
					/*后面这个是否变了?*/
					current_state->assign(*g_initial_state);
					if(g_display)
					{
						current_state->dump();
					}
					/*和subplan.insert有什么区别?*/
					plan.insert(plan.end(),subplan.begin(),subplan.end());

					//check plan
					bool fill_in = false; //this variable determines if the previous plan satisfies current initial state
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
							/*?*/
							last_modified++;
							if(g_display)
							{
										/*cout << "final state:" << endl;
										check_plan_state->dump();
										dump_goal();*/
								cout << "previous plan satisfies current initial state " << endl;
							}
							previous_state->assign(*g_initial_state);
							prev_values = new_values;
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
					/*?*/
					last_modified = 0;
		//			plan.insert(plan.end(),subsubengine->get_plan().begin(),subsubengine->get_plan().end());
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
						/*?操作对当前状态是一致性可适用*/
						if(g_operators[j].is_conformant_applicable(*current_state))
						{
							vector<pair <int, int> > sub_goal;
							vector<const Operator *> sub_plan;					
							/*子目标为动作的前置条件or effect 条件? 可适用是condition_sub_goal*/
							sub_goal = g_operators[j].condition_sub_goal(*previous_state);
							/*?*/
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
								//cout << "subsub 1 " << endl;
								/*这个插入不是只插入一部分吗?*/
								if(subsubengine->found_solution())
								{
									sub_plan = subsubengine->get_plan();
									/*insert(a,b,c)  将b-c插入到a位置*/
									plan.insert(plan.begin()+i,subsubengine->get_plan().begin(),subsubengine->get_plan().end());
									if(g_display)
									{
										cout << "insert the following actions into plan:" << endl;
									}
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
										/*当前状态后移*/
										current_state->assign(State(*current_state, g_operators[h]));
									}
									i=i+subsubengine->get_plan().size();
								}
								else
								{
									maintain_maximum = false;
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
						/*不是一致性可适用?*/
						else
						{
							//cout << "not applicable";
							//g_operators[j].dump();
							vector<pair <int, int> > sub_goal;
							/*不可适用是conformant_sub_goal*/
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

							//cout << " subsub 2" << endl;
							if (!subsubengine->found_solution())
							{
								if(g_display) 
								{
									cout << "No plan was found. Backtracking." << endl;
								}
								return false;
							}
							sub_plan = subsubengine->get_plan();
							plan.insert(plan.begin()+i,subsubengine->get_plan().begin(),subsubengine->get_plan().end());
							if(g_display)
							{
								cout << "insert the following actions into plan:" << endl;
							}
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
					/*再找一遍，看经过上面的操作后，最终到达了哪一步*/
					subsubengine = search_subplan(current_state,g_goal,true,true);

					if (!subsubengine->found_solution())
					{
						if(g_display) 
						{
							cout << "No plan was found. Backtracking." << endl;
						}
						return false;
					}
					prev_values = new_values;
					//restore values
					g_initial_state->vars = g_original_values;
					//restore values
					for(int i=0;i<prev_values.size();i++)
					{
						g_initial_state->negate_var(prev_values[i].first);
					}
					new_values = vector<pair<int, int> > ();
					subplan.clear();
					/*将新找到的完全插入*/
					subplan.insert(subplan.end(),subsubengine->get_plan().begin(),subsubengine->get_plan().end());
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

				int var,val;
				var = -1;			
				for(int i = 0 ; i < g_variable_name.size() ; i++)
				{
					if(name.find(g_variable_name[i]) == 0 && name.size() == g_variable_name[i].size()+1)
					{
						var = i;
						cout << g_variable_name[i]<<" ";
					}
				}
				getline(infile, name);
				stringstream ss(name);
				ss >> val;
				cout << val << endl;
				if (var!=-1) {
					g_initial_state->set_var(var,val);
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
    
	
	if(!valid_plan) return false;
    ofstream outfile;
    outfile.open("finalplan", ios::out);
    cout << "final plan: plan_size "<<plan.size()<< endl;
    for(int k=0;k<plan.size();k++)
    {
		cout << plan[k]->get_name() << endl;
		outfile << plan[k]->get_name() << endl;
    }
     outfile.close();     

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


