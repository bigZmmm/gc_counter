/*********************************************************************
 * Author: Malte Helmert (helmert@informatik.uni-freiburg.de)
 * (C) Copyright 2003-2004 Malte Helmert
 * Modified by: Silvia Richter (silvia.richter@nicta.com.au)
 * (C) Copyright 2008 NICTA
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

#ifndef OPERATOR_H
#define OPERATOR_H

#include <cassert>
#include <iostream>
#include <string>
#include <vector>

#include "globals.h"
#include "state.h"

class Variable;

struct Prevail {
    int var;
    int prev;
    Prevail(std::istream &in);
    Prevail(int v, int p) : var(v), prev(p) {}

    bool is_applicable(const State &state) const {
	assert(var >= 0 && var < g_variable_name.size());
	assert(prev >= 0 && prev < g_variable_domain[var]);
	return state[var] == prev;
    }

    void dump() const;
};

struct PrePost {
    int var;
    int pre, post;
    std::vector<Prevail> cond;
    PrePost() {} // Needed for axiom file-reading constructor, unfortunately.
    PrePost(std::istream &in);
    PrePost(int v, int pr, int po, const std::vector<Prevail> &co)
	: var(v), pre(pr), post(po), cond(co) {}

    bool is_applicable(const State &state) const {
	assert(var >= 0 && var < g_variable_name.size());
	assert(pre == -1 || (pre >= 0 && pre < g_variable_domain[var]));
	return pre == -1 || state[var] == pre;
    }

    bool does_fire(const State &state) const {
	for(int i = 0; i < cond.size(); i++)
	    if(!cond[i].is_applicable(state))
		return false;
	return true;
    }

    void dump() const;
};

class Operator {
    bool is_an_axiom;
    std::vector<Prevail> prevail;      // var, val
    std::vector<PrePost> pre_post;     // var, old-val, new-val, effect conditions
    std::string name;
    int cost;
public:
    Operator(std::istream &in, bool is_axiom);
    int index_number;
    void dump() const;
    std::string get_name() const {return name;}
    bool is_axiom() const {return is_an_axiom;}

    const std::vector<Prevail> &get_prevail() const {return prevail;}
    const std::vector<PrePost> &get_pre_post() const {return pre_post;}

    bool is_applicable(const State &state) const {
		for(int i = 0; i < prevail.size(); i++)
			if(!prevail[i].is_applicable(state))
			return false;
		for(int i = 0; i < pre_post.size(); i++)
			if(!pre_post[i].is_applicable(state))
			return false;
		return true;
    }

    bool need_checking_all_conditions() const {
		if (prevail.size()==0)
		{
			return false;
		}
		else
		{
			for(int i=0;i<prevail.size();i++)
				for(int j=0;j<pre_post.size();j++)
					if(prevail[i].var == pre_post[j].var) return true;
		}
		return false;
    }

    bool is_conformant_applicable(const State &state) const {
		/*前置条件不为空*/
		if(need_checking_all_conditions())
		{
			for(int i = 0; i < prevail.size(); i++)
				if(!prevail[i].is_applicable(state))
				return false;
			for(int i = 0; i < pre_post.size(); i++)
			{
			if(!pre_post[i].is_applicable(state))
				return false;
			if(!pre_post[i].does_fire(state))
				return false;
			}
			return true;
		}
		else
		{	
			for(int i = 0; i < prevail.size(); i++)
			{
			if(!prevail[i].is_applicable(state))
				return false;
			}
			return true;
		}
    }

    vector<pair <int,int> > conformant_sub_goal(const State &state) const {
		vector<pair <int,int> > sub_goal;	
		for(int i = 0; i < prevail.size(); i++) 
			if(!prevail[i].is_applicable(state))
				sub_goal.push_back(make_pair(prevail[i].var,prevail[i].prev));
		if(need_checking_all_conditions())
		{
			for(int i=0;i < pre_post.size(); i++)
				for(int j=0;j < pre_post[i].cond.size();j++)
						if(!pre_post[i].cond[j].is_applicable(state))
						sub_goal.push_back(make_pair(pre_post[i].cond[j].var,pre_post[i].cond[j].prev));
		}
		return sub_goal;
    }

    vector<pair <int,int> > condition_sub_goal(const State &state) const {
		vector<pair <int,int> > sub_goal;	
		for(int i=0; i < pre_post.size(); i++)
		{
			if(pre_post[i].cond.size()>1)
			{
				sub_goal.clear();
				return sub_goal;
			}
			if(pre_post[i].does_fire(state))
			{
				for(int j=0;j < pre_post[i].cond.size();j++)
					sub_goal.push_back(make_pair(pre_post[i].cond[j].var,pre_post[i].cond[j].prev));
			}
		}
		return sub_goal;
    }


    int get_cost() const {return cost;}
};

#endif
