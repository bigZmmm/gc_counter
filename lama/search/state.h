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

#ifndef STATE_H
#define STATE_H

#include <iostream>
#include <vector>
#include <ext/hash_set>
#include "landmarks_types.h"
#include "globals.h"


using namespace std;
using namespace __gnu_cxx;

class Operator;
class PrePost;
class LandmarkNode;

class State {
    friend void read_everything(istream &in, bool generate_landmarks, bool reasonable_orders);

//    vector<int> vars; // values for vars
    hash_set<const LandmarkNode *, hash_pointer> reached_lms;
//    int reached_lms_cost;

//    int g_value; // min. cost of reaching this state from the initial state
//    void set_landmarks_for_initial_state();
    void update_reached_lms(const Operator &op);
    bool landmark_is_leaf(const LandmarkNode& node, 
			  const hash_set<const LandmarkNode*, hash_pointer>& reached) const;
    bool check_lost_landmark_children_needed_again(const LandmarkNode& node) const;
    
public:
//addin
    /*var就是所有的fact*/
    vector<int> vars; // values for vars
    int reached_lms_cost;

    int g_value; // min. cost of reaching this state from the initial state

    void set_landmarks_for_initial_state();

    //addin
    State();

    State(istream &in);
    State(const State &predecessor, const Operator &op);

    /*使当前变量的值为最大值减1，如：总共5个值则设置为4
        表示为<none of those>*/
    void negate_var(int index){
	    vars[index] = g_variable_domain[index]-1;
    }
    void set_var(int index, int value) {
	    vars[index] = value;
    }
    int &operator[](int index) {
	    return vars[index];
    }
    int operator[](int index) const {
	    return vars[index];
    }

    //addin
    void assign(State s);
    bool isOneState(State s);

    void dump() const;
    bool operator<(const State &other) const;
    bool satisfy_subgoal(vector<pair <int, int> >) const;

    int get_g_value() const {return g_value;}
    void change_ancestor(const State &new_predecessor, const Operator &new_op);

    int check_partial_plan(hash_set<const LandmarkNode*, hash_pointer>& reached) const;
    int get_needed_landmarks(hash_set<const LandmarkNode*, hash_pointer>& needed) const;
};

#endif
