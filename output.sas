begin_metric
0
end_metric
begin_variables
8
var0 2 -1
var1 2 -1
var2 2 -1
var3 2 -1
var4 2 -1
var5 2 -1
var6 2 0
var7 2 -1
end_variables
begin_state
1
1
1
1
0
1
1
0
end_state
begin_goal
1
6 0
end_goal
5
begin_operator
can_move 
0
3
1 1 1 3 -1 0
1 2 1 3 -1 0
2 1 0 2 0 3 -1 1
0
end_operator
begin_operator
north 
0
5
2 3 0 5 0 2 -1 0
2 2 0 3 0 2 -1 1
0 3 -1 1
2 3 0 5 0 5 -1 1
2 2 0 3 0 7 -1 0
0
end_operator
begin_operator
south 
0
5
2 3 0 7 0 2 -1 0
2 2 0 3 0 2 -1 1
0 3 -1 1
2 2 0 3 0 5 -1 0
2 3 0 7 0 7 -1 1
0
end_operator
begin_operator
east 
0
5
2 3 0 4 0 0 -1 0
2 0 0 3 0 0 -1 1
2 0 0 3 0 1 -1 0
0 3 -1 1
2 3 0 4 0 4 -1 1
0
end_operator
begin_operator
west 
0
5
2 1 0 3 0 0 -1 0
2 0 0 3 0 0 -1 1
2 1 0 3 0 1 -1 1
0 3 -1 1
2 0 0 3 0 4 -1 0
0
end_operator
2
begin_rule
1
7 0
6 1 0
end_rule
begin_rule
1
0 0
6 1 0
end_rule
