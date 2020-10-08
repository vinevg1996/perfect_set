#!/usr/bin/python
from z3 import *
from combinatorics import Combinatorics
from simplePaths import SimplePaths
from operator import mul

print "_______________________"
print "_______________________"
print "_______________________"
print "z3 starts working"
print "_______________________"

def fill_simplePathArrays(solver, hostsMaska, simplePaths, simplePathArrays):
    for i in range(0, len(hostsMaska)):
        for j in range(0, len(hostsMaska[i])):
            if (hostsMaska[i][j] == 1):
                for k in range(0, len(simplePaths[i][j])):
                    solver.add(simplePathArrays[i][j][k][0] == len(simplePaths[i][j][k]))
                    for l in range(0, len(simplePaths[i][j][k])):
                        solver.add(simplePathArrays[i][j][k][l + 1] == simplePaths[i][j][k][l])
    return

def print_from_solver_model_str(solver_model_str, pattern):
    flag = True
    fin_id = 0
    while flag:
        start_id = solver_model_str.find(pattern, fin_id)
        if start_id == -1:
            flag = False
        else:
            fin_id = solver_model_str.find(",", start_id)
            print solver_model_str[start_id : fin_id]
    return

def return_from_solver_model_str(solver_model_str, pattern):
    pattern_list = []
    flag = True
    fin_id = 0
    while flag:
        start_id = solver_model_str.find(pattern, fin_id)
        if start_id == -1:
            flag = False
        else:
            fin_id = solver_model_str.find(",", start_id)
            #print solver_model_str[start_id : fin_id]
            pattern_list.append(solver_model_str[start_id : fin_id])
    return pattern_list

def is_not_covered(path1, path2, switch_number):
    bool_matrix = [[False for y in range(0, switch_number)] for x in range(0, switch_number)]
    for i in range(0, len(path1) - 1):
        bool_matrix[path1[i]][path1[i + 1]] = True
    for i in range(0, len(path2) - 1):
        if (bool_matrix[path2[i]][path2[i + 1]] == True):
            return False
    return True

#ids_0_1 = 1
def parse_ids_string(str_ids):
    split_space_str_ids = str_ids.split(' ')
    value = split_space_str_ids[2]
    split_str_ids = split_space_str_ids[0].split('_')
    row = split_str_ids[1]
    col = split_str_ids[2]
    return [int(row), int(col), int(value)]

def verify_perfect_set(simplePaths, list_ids, switch_number):
    print "paths:"
    for ids in list_ids:
        [row, col, value] = parse_ids_string(ids)
        path = simplePaths.hostSimplePathsMatrix[row][col][value]
        print "path: ", path
    i = 0
    flag = True
    while (i < len(list_ids)) and (flag):
        [row_1, col_1, value_1] = parse_ids_string(list_ids[i])
        path1 = simplePaths.hostSimplePathsMatrix[row_1][col_1][value_1]
        j = i + 1
        while (j < len(list_ids)) and (flag):
            [row_2, col_2, value_2] = parse_ids_string(list_ids[j])
            path2 = simplePaths.hostSimplePathsMatrix[row_2][col_2][value_2]
            if (path1[0:2] != path2[0:2]) and (path1[len(path1) - 2 :] != path2[len(path2) - 2 :]):
                flag = is_not_covered(path1[1 : len(path1) - 1], path2[1 : len(path2) - 1], switch_number)
                if (flag == False):
                    print "path1: ", path1
                    print "path2: ", path2
            j = j + 1
        i = i + 1
    return flag

#hosts = [[0, 0], [1, 1], [2, 2]]
hosts = [[0, 0], [1, 0], [2, 1], [3, 2]]
simplePaths = SimplePaths(3, 4)
simplePaths.GenerateAllSimplePaths()
simplePaths.SetHosts(hosts)
simplePaths.GenerateAllHostSimplePaths()
print "HostsSimplePathsMatrix"
simplePaths.PrintHostsSimplePathsMatrix()
#simplePaths.hostSimplePathsMatrix
#print simplePaths.hostSimplePathsMatrix
print "______________________"

hostsMaska = [[0, 0, 1, 1], [0, 0, 1, 1], [1, 1, 0, 1], [1, 1, 1, 0]]

Paths = [[Array('paths_%d_%d' % (i, j), IntSort(), ArraySort(IntSort(), IntSort())) 
          for j in range(0, 4)] for i in range(0, 4)]

solver = Solver()
fill_simplePathArrays(solver, hostsMaska, simplePaths.hostSimplePathsMatrix, Paths)

ids = [[Int('ids_%d_%d' % (i, j)) for j in range(0, 4) ] for i in range(0, 4) ]

x_var = [[Int('x_var_%d_%d' % (i, j)) for j in range(0, 4) ] for i in range(0, 4) ]

for i in range(0, 4):
    for j in range(0, 4):
        if hostsMaska[i][j] == 1:
            solver.add(ids[i][j] >= 0)
            solver.add(ids[i][j] < len(simplePaths.hostSimplePathsMatrix[i][j]))

map_number_to_i_j = list()
map_number_to_i_j.append([0, 2])
map_number_to_i_j.append([0, 3])
map_number_to_i_j.append([1, 2])
map_number_to_i_j.append([1, 3])
map_number_to_i_j.append([2, 0])
map_number_to_i_j.append([2, 1])
map_number_to_i_j.append([2, 3])
map_number_to_i_j.append([3, 0])
map_number_to_i_j.append([3, 1])
map_number_to_i_j.append([3, 2])

i = 0
while i < len(map_number_to_i_j):
    row_1 = map_number_to_i_j[i][0]
    col_1 = map_number_to_i_j[i][1]
    path_i = Paths[row_1][col_1][ids[row_1][col_1]]
    len_x = path_i[0]
    j = i + 1
    while j < len(map_number_to_i_j):
        row_2 = map_number_to_i_j[j][0]
        col_2 = map_number_to_i_j[j][1]
        path_j = Paths[row_2][col_2][ids[row_2][col_2]]
        len_y = path_j[0]
        x = x_var[row_1][col_1]
        y = x_var[row_2][col_2]
        w0 = And(Or(path_i[1] != path_j[1], 
                    path_i[2] != path_j[2]), 
                 Or(path_i[len_x - 1] != path_j[len_y - 1],
                    path_i[len_x] != path_j[len_y]))
        w1 = ForAll([x, y], Implies(
                    And(x >= 1, x < len_x - 1, y >= 1, y < len_y - 1),
                    Or((path_i[x] != path_j[y]), (path_i[x + 1] != path_j[y + 1]))
                    ))
        w_01 = Implies(w0, w1)
        solver.add(w_01)
        j = j + 1
    i = i + 1

print solver.check()
if solver.check() == z3.sat:
    solver_model_str = str(solver.model())
    print_from_solver_model_str(solver_model_str, "ids")
    indexes = return_from_solver_model_str(solver_model_str, "ids_")
    print verify_perfect_set(simplePaths, indexes, 3)

'''
solver_check = solver.check()
print "solver_check = ", solver_check
#while solver.check() == z3.sat:
if solver_check == z3.sat:
    solver_model_str = str(solver.model())
    print_from_solver_model_str(solver_model_str, "ids_1_0")
    print_from_solver_model_str(solver_model_str, "ids_2_1")
    print_from_solver_model_str(solver_model_str, "x_var_1_0")
    print_from_solver_model_str(solver_model_str, "x_var_2_1")
    solver.add(Or(ids[1][0] != solver.model()[ids[1][0]], 
                  ids[2][1] != solver.model()[ids[2][1]]))
'''