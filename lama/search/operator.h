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
	/*var:变量名 prev:变量需要满足*/
    int var;
    int prev;
    Prevail(std::istream &in);
    Prevail(int v, int p) : var(v), prev(p) {}
	/*判断该状态变量是否和这个prevail一样*/
    bool is_applicable(const State &state) const {
		assert(var >= 0 && var < g_variable_name.size());
		assert(prev >= 0 && prev < g_variable_domain[var]);
		return state[var] == prev;
    }

    void dump() const;
};

struct PrePost {
	/*var：变量名 pre：变量需要满足 post：满足pre后改变为*/
    int var;
    int pre, post;
	/*条件影响*/
    std::vector<Prevail> cond;
    PrePost() {} // Needed for axiom file-reading constructor, unfortunately.
    PrePost(std::istream &in);
    PrePost(int v, int pr, int po, const std::vector<Prevail> &co)
	: var(v), pre(pr), post(po), cond(co) {}

	/*这个变量满足，或者本就不需要满足*/
    bool is_applicable(const State &state) const {
		assert(var >= 0 && var < g_variable_name.size());
		assert(pre == -1 || (pre >= 0 && pre < g_variable_domain[var]));
		/*条件影响为空，或者是该状态的变量是否和这个pre一样*/
		return pre == -1 || state[var] == pre;
    }
	/*满足所有的条件影响*/
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
	/*一种情况：var相同并且 post=val*/
	bool isadd(int var,int val,int i)const {
		bool flag =false;
		// cout<<"add:"<<var<<"-"<<pre_post[i].var<<" "<<val<<"-"<<pre_post[i].post<<endl;
		if(((var==pre_post[i].var)&&(val==pre_post[i].post))){
			flag=true;
			// cout<<"falg:"<<flag<<endl;
		}
		return flag;
	}
	/*三种情况：1.var相同且pre=val 2.pre=-1，cond中存在var=var,val=prev 3.var相同但是post不为val*/
	/*如果pre-post！=-1，则不在这个的情况内*/
	bool isdel(int var,int val,int i) const {
		bool flag =false;
		int j;
		if((pre_post[i].var==var)&&(pre_post[i].post!=val)){
			if(pre_post[i].pre==val){
				flag=true;
			}else if(pre_post[i].pre==-1){
				/*判断条件影响*/
				for(j=0;j<pre_post[i].cond.size();j++){
					if((pre_post[i].cond[j].var==var)&&(pre_post[i].cond[j].prev==val))
						flag=true;
				}
				/*因为互斥组的存在，这个是成立的，能证明在下一步中，这个值是不存在的*/
				if(pre_post[i].post!=val)
					flag = true;
			}
		}
		return flag;
	}
    const std::vector<Prevail> &get_prevail() const {return prevail;}
    const std::vector<PrePost> &get_pre_post() const {return pre_post;}
	
	/*相当于正常的前置条件*/
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
			/*前置条件的变量和effect中需变化的变量是一样的*/
			for(int i=0;i<prevail.size();i++)
				for(int j=0;j<pre_post.size();j++)
					if(prevail[i].var == pre_post[j].var) return true;
		}
		return false;
    }
	/*原：如果前置条件不包含effect中需变化的变量，只需检查前置条件，否则两个都需要检查（并且要检查条件影响）*/
	
	/*修改为只判断前提条件*/
    bool is_conformant_applicable(const State &state) const {
		/*前置条件的变量和effect中需变化的变量是一样的*/
		if(need_checking_all_conditions())
		{
			for(int i = 0; i < prevail.size(); i++)
				if(!prevail[i].is_applicable(state))
					return false;
			for(int i = 0; i < pre_post.size(); i++)
			{
				if(!pre_post[i].is_applicable(state))
					return false;
				/*比is_applicable多出来的-条件影响*/
				// if(!pre_post[i].does_fire(state))
				// 	return false;
			}
			return true;
		}
		/*否则只需要检查前置条件就行*/
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
	/*添加不满足的条件为子目标*/
    vector<pair <int,int> > conformant_sub_goal(const State &state) const {
		vector<pair <int,int> > sub_goal;	
		/*只需要满足前置条件*/
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

	/*添加该动作在上个状态时的条件影响*/
    vector<pair <int,int> > condition_sub_goal(const State &state) const {
		vector<pair <int,int> > sub_goal;	
		for(int i=0;i<prevail.size();i++){
			sub_goal.push_back(make_pair(prevail[i].var,prevail[i].prev));
		}

		for(int i=0; i < pre_post.size(); i++)
		{
			// if(pre_post[i].cond.size()>1)
			// {
			// 	sub_goal.clear();
			// 	return sub_goal;
			// }
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
