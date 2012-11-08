#!/usr/bin/python

def traverse_c(program, l1, equals, not_equals) :
	for l in l1 :
		assert isinstance(l, int)
	
	for i in range(len(l1)) :
		for j in range(len(l1)) :
			if j > i :
				assert l1[j] != l1[i]
	
	for i in range(len(l1)) :
		l0 = []
		for j in range(i) :
			l0 += ["_" + str(j)]
		for j in range(len(l1) - i) :
			l0 += [l1[j]]
		
		assert len(l0) == len(l1)

		not_equals_l0 = []

		for j in range(len(l1)) :
			for k in range(len(l1)) :
				if k > j :
					not_equals_l0 += [[l0[k], l0[j]]]
		
		equals_l0 = []
		for l in l0 :
			equals_l0 += [[l, l]]

		not_equals_nums = []
		for j in [j for j in l0 if isinstance(j, int)] :
			for k in [i["addr"] for i in program if isinstance(i["addr"], int)] :
				if k != j :
					not_equals_nums += [[k, j]]

			

		if traverse(program, l0, equals + equals_l0, not_equals + not_equals_l0 + not_equals_nums) :
			return True
	
	return False


def traverse(program, l1, equals, not_equals):
	assert len(l1) == 4

	for i in range(len(l1)) :
		for j in range(len(l1)) :
			if j > i :
				assert l1[i] != l1[j]


	if len(program) == 0 :
		print("EQUALS =", equals)
		print("NOT_EQUALS =", not_equals)
		print_model(equals, not_equals)
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
					neq)
			return False

		if program[0]["l1"] == "hit" :
			for i in range(len(l1)) :
				e = l1[i]
				if sat(equals + [[addr, e]], not_equals) :
					if traverse(
						program[1:],
						[e] + l1[:i] + l1[i+1:], 
						equals + [[addr, e]],
						not_equals) :
						return True

			return False
				
	else :
		return traverse(program[1:], l1, equals, not_equals)

########################################

def sat(equals, not_equals) :
	# assert equals is a list of pairs (a pair is a list of 2 elements)
	for eq in equals :
		assert len(eq) == 2
	# assert not_equals is a list of pairs
	for neq in not_equals :
		assert len(neq) == 2

	

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


def print_model(equals, not_equals) :
	elems_classes = get_eqclasses(equals)
	# elems_classes is a list of sets

	print("EQCLASSES =", elems_classes)

	if len(elems_classes) == 0 :
		print("elems_classes is empty :( nothing to print")

	values = {}
	used_values = []
	second_classes = []
	for eq_class in elems_classes :
		# eq_class is a set
		ints = [x for x in eq_class if isinstance(x, int)]
		if len(ints) > 0 :
			value = ints[0]
			used_values += [value]
			for a in eq_class :
				if not isinstance(a, int) :
					values[a] = value
		else :
			second_classes += [eq_class]
	
	if len(used_values) > 0 :
		value = max(used_values) + 1
	else :
		value = 0

	for eq_class in second_classes :
		for a in eq_class :
			values[a] = value
		value = value + 1

	for a in values :
		print(a, '=', values[a])
			
##################################################

# gets a list of pairs (a pair is a list of 2 values)
# returns a list of equivalence classes (eqclass is a set of values) 
def get_eqclasses(equals) :
	if len(equals) == 0 :
		return []
	
	prevpairs = []
	newpairs = [equals[0]]
	while newpairs != prevpairs :
		eqclass = set([i for p in newpairs for i in p])
		prevpairs = newpairs
		newpairs = [p for p in equals
					if p[0] in eqclass 
					or p[1] in eqclass ]
	return [eqclass] + get_eqclasses([p for p in equals if p not in newpairs])


#################################################

template = [
	{"l1" : "miss", "addr": "x"},
	{"l1" : "hit", "addr" : 65},
	{"l1": "hit", "addr" : "a1"},
	{"l1" : "hit", "addr" : "a2"},
	{"l1" : "hit", "addr" : "a3"},
	{"l1" : "hit", "addr" : "a4" }
	, {"l1" : "miss", "addr" : "c" }
]

# lru element is the last element of this seq
initial_l1 = [1, 2, 3, 4]

equals = [[i["addr"], i["addr"]] for i in template]

# alldiffs_l1 = [ [initial_l1[i], initial_l1[j]]
#			for i in range(len(initial_l1))
#			for j in range(len(initial_l1))
#			if j > i ]

# not_equals = [["a1", "a2"], ["a2", "a3"], ["a3", "a4"]]
# not_equals = [["a1", "a2"], ["a1", "a3"], ["a1", "a4"],
#				["a2", "a3"], ["a3", "a4"]]

not_equals = [["a1", "a2"], ["a1", "a3"], ["a1", "a4"],
			["a2", "a3"], ["a2", "a4"], ["a3", "a4"]]

if not traverse_c(template, initial_l1, equals, not_equals ) :
	print("template is unsatisfiable")

