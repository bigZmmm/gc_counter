begin_metric
0
end_metric
begin_variables
9
var0 2 0
var1 2 -1
var2 2 -1
var3 2 -1
var4 2 -1
var5 2 -1
var6 2 -1
var7 2 -1
var8 2 -1
end_variables
begin_state
1
0
1
0
0
0
1
1
0
end_state
begin_goal
1
0 0
end_goal
4
begin_operator
fwd 
0
4
1 3 0 2 -1 0
1 2 0 2 -1 1
1 2 0 3 -1 0
1 3 0 3 -1 1
0
end_operator
begin_operator
bwd 
0
4
1 3 0 2 -1 0
1 2 0 2 -1 1
1 2 0 3 -1 0
1 3 0 3 -1 1
0
end_operator
begin_operator
close 
0
2
1 3 0 5 -1 0
1 2 0 8 -1 0
0
end_operator
begin_operator
lock 
0
2
3 1 1 3 0 5 0 6 -1 0
3 8 0 2 0 4 1 7 -1 0
0
end_operator
4
begin_rule
4
8 0
1 0
4 0
5 0
0 1 0
end_rule
begin_rule
4
8 0
4 0
5 0
6 0
0 1 0
end_rule
begin_rule
4
8 0
5 0
6 0
7 0
0 1 0
end_rule
begin_rule
4
8 0
1 0
5 0
7 0
0 1 0
end_rule
