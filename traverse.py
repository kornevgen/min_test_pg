#!/usr/bin/python

def traverse(program, l1, equals, not_equals, needed_addrs):
	assert len(l1) == 4
	# assert all_different(elements of l1) 

	if len(program) == 0 :
		print_minimal_model(equals, not_equals, needed_addrs)
		return True

	addr = program[0]["addr"];

	if "l1" in program[0] :
		if program[0]["l1"] == "miss" :
			neq = not_equals + [[addr, x] for x in l1]
			if sat(equals, neq) :
				return traverse(
					program[1:],
					[addr] + l1[:-1],
					equals,
					neq,
					needed_addrs + l1 + [addr])
			return False

		if program[0]["l1"] == "hit" :
			for i in range(len(l1)) :
				e = l1[i]
				if sat(equals + [[addr, e]], not_equals) :
					if traverse(
						program[1:],
						[e] + l1[:i] + l1[i+1:], 
						equals + [[addr, e]],
						not_equals,
						needed_addrs + [e, addr]) :
						return True

			return False
				
	else :
		return traverse(program[1:], l1, equals, not_equals, needed_addrs)

########################################

def sat(equals, not_equals) :
	# assert equals is a list of pairs (a pair is a list of 2 elements)
	# assert not_equals is a list of pairs

	for c in not_equals :
		if exists_path(c[0], c[1], equals) :
			return False
	return True

def exists_path(start, finish, edges) :
	if start == finish :
		return True

	for edge_n in range(len(edges)) :
		edge = edges[edge_n]
		edges_without = edges[:edge_n] + edges[edge_n+1:]
		if start == edge[0] and exists_path(edge[1], finish, edges_without) :
			return True
		elif start == edge[1] and exists_path(edge[0], finish, edges_without) :
			return True
	return False	


def print_minimal_model(equals, not_equals, needed_addrs) :
	equiv_classes0 = get_equiv_classes(equals)
		# a class is a list of pairs
		# equiv_classes is a list of classes

	equiv_classes1 = minimize(equiv_classes0, not_equals)

	elems_classes = setof_elements(equiv_classes1)
	# elems_classes is a list of sets
	
	if len(elems_classes) == 0 :
		print("elems_classes is empty :( nothing to print")

	values = {}
	for i, eq_class in enumerate(elems_classes) :
		for e in eq_class :
			values[e] = i

	n = len(elems_classes)
	for a in set(needed_addrs) :
		if a not in values : # for initial elements of cache
			values[a] = n
			n = n + 1
		print(a, '=', values[a])
			
			
# gets a list of classes (a class is a list of pairs)
# returns a list of sets (a "set" is a set of elements of a class)  
def setof_elements(listof_classes) :
	elems_classes = []
	for eq_class in listof_classes :
		e_class = []
		for pair in eq_class :
			e_class = e_class + [pair[0], pair[1]]
		elems_classes = elems_classes + [set(e_class)]
	return elems_classes

# gets a list of classes (a class is a list of pairs)
# returns a list of combined classes (if class1 and class2 can be merged, they are merged)
# NB: this is not optimal implementation of minimize function!
def minimize(equiv_classes, not_equals) :
	for i in range(len(equiv_classes)) :
		for j in range(len(equiv_classes)) :
			if j > i :
				new_eq = equiv_classes[i] + equiv_classes[j] + [[equiv_classes[i][0][0] , equiv_classes[j][0][0]]]
				if sat(new_eq, not_equals) :
					return minimize([new_eq] + equiv_classes[:i] + equiv_classes[i+1:j] + equiv_classes[j+1:], not_equals)
	# equiv_classes are already minimized
	return equiv_classes

##################################################

# gets a list of pairs
# returns a list of equivalence classes (a class is a list of pairs)
def get_equiv_classes(equals) :
	if len(equals) == 0 :
		return []

	pair = equals[0]
	e_class = [p for p in equals if p[0] in pair or p[1] in pair]
	return [e_class] + get_equiv_classes([p for p in equals if (p not in e_class)])
				

#################################################

template = [
	{"l1": "hit", "addr" : "a1"},
	{"l1" : "hit", "addr" : "a2"},
	{"l1" : "hit", "addr" : "a3"},
	{"l1" : "hit", "addr" : "a4" },
	{"l1" : "miss", "addr" : "c" }
]

# lru element is the last element of this seq
initial_l1 = ["c1", "c2", "c3", "c4"]

alldiffs_l1 = [ [initial_l1[i], initial_l1[j]]
			for i in range(len(initial_l1))
			for j in range(len(initial_l1))
			if j > i ]

equiv_pairs = [[op["addr"], op["addr"]] for op in template] 

equals = equiv_pairs
# equals = equiv_pairs + [["a1", "c"]]
# not_equals = alldiffs_l1 + [["a1", "a2"], ["a2", "a3"], ["a3", "a4"]]
# not_equals = alldiffs_l1 + [["a1", "a2"], ["a1", "a3"], ["a1", "a4"],
#				["a2", "a3"], ["a3", "a4"]]

not_equals = alldiffs_l1 + [["a1", "a2"], ["a1", "a3"], ["a1", "a4"],
				["a2", "a3"], ["a2", "a4"], ["a3", "a4"]]

if not traverse(template, initial_l1, equals, not_equals, [] ) :
	print("template is unsatisfiable")

