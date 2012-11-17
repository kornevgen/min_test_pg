#!/usr/bin/python

def traverse_c(program, l1, equals, not_equals) :
	for l in l1 :
		assert isinstance(l, int)
	
	for i in range(len(l1)) :
		for j in range(len(l1)) :
			if j > i :
				assert l1[j] != l1[i]

	for i in range(len(l1)+1) :
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

		nums = [j for j in 
				l0 +
				[i["addr"] for i in program if "addr" in i] +
				[i["remvd"] for i in program if "remvd" in i]
		if isinstance(j, int)]

		not_equals_nums = []
		for j in nums :
			for k in nums :
				if k != j :
					not_equals_nums += [[k, j]]

		# try heuristics
		eq = equals + equals_l0
		neq = not_equals + not_equals_l0 + not_equals_nums
		remvd_neqs(program, l1, eq, neq)  # equals and not_equals may be increased
		if sat(eq, neq) :
			if traverse(program, l0, eq, neq) :
				return True
	
	return False


def traverse(program, l1, equals, not_equals):
	assert len(l1) == 4

	for i in range(len(l1)) :
		for j in range(len(l1)) :
			if j > i :
				assert l1[i] != l1[j]


	if len(program) == 0 :
		print_model(equals, not_equals)
		return True

	print(" ")
	print("left: ", len(program), "program elements")
	print("cache:", l1)

	addr = program[0]["addr"];

	if "l1" in program[0] :
		if program[0]["l1"] == "miss" :
			print("try miss(", addr, ")")
			neq = not_equals + [[addr, x] for x in l1]
			eq = [[program[0]["remvd"],l1[-1]]] if "remvd" in program[0] else []
			
			if "remvd" in program[0] :
				print("remvd: ", program[0]["remvd"], "=", l1[-1])

			if False and len(program) == 1 :
				print("TRY SAT:")
				print("EQ = ", equals + eq)
				print("NotEQ = ", neq)
			
			if sat(equals+eq, neq) :
				return traverse(
					program[1:],
					[addr] + l1[:-1],
					equals + eq,
					neq)

		if program[0]["l1"] == "hit" :
			ind = index(addr, l1, equals)
			if ind != -1 :
				if traverse(program[1:], [addr] + l1[:ind] + l1[ind+1:], equals, not_equals) :
					return True
			else :
				for i in range(len(l1)) :
					e = l1[i]
					print("try hit: ", addr, "=", e)
					if sat(equals + [[addr, e]], not_equals) :
						if traverse(
							program[1:],
							[e] + l1[:i] + l1[i+1:], 
							equals + [[addr, e]],
							not_equals) :
							return True
					else :
						print("unsat; try next or backtrack")

		if program[0]["l1"] == "any" :
			program[0]["l1"] = "miss"
			if traverse(program, l1, equals, not_equals) :
				return True
			program[0]["l1"] = "hit"
			if traverse(program, l1, equals, not_equals) :
				return True
			program[0]["l1"] = "any"

		print("backtrack")	
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


def index(addr, l1, eqs) :
	for i in range(len(l1)) :
		if eq(addr, l1[i], eqs) :
			return i
	return -1

def eq(x, y, eqs) :
	return exists_path(x, y, eqs)

def print_model(equals, not_equals) :
	elems_classes = get_eqclasses(equals)
	# elems_classes is a list of sets

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

def remvd_neqs(program, l1, equals, not_equals) :
	w = len(l1)

	for i in range(len(program)) :
		if "remvd" in program[i] :
			rmvd_adr = program[i]["remvd"]
			in_l1 = []
			remvd_l1 = []
			j = i-1
			while j >= 0 and len(in_l1) < w-1 :
				if "l1" in program[j] :
					if not is_known(program[j]["addr"], in_l1, equals) :
						in_l1 += [program[j]["addr"]]
					if "remvd" in program[j] :
						remvd_l1 += [program[j]["remvd"]]
				j = j - 1

			if len(in_l1) < w-1:
				k = 0
				while len(in_l1) < w - 1 :
					if not is_known(l1[k], in_l1, equals) :
						in_l1 += [l1[k]]
					k += 1

			not_equals += [[rmvd_adr, a] for a in in_l1 + remvd_l1]
													

def is_known(x, l, equals) :
	for i in l :
		if exists_path(x, i, equals) :
			return True
	return False

#################################################

template0 = [
	{"l1" : "miss", "addr": "x", "remvd": "y" }, # 5 },
	{"l1" : "hit", "addr" : 65},
	{"l1": "hit", "addr" : "a1"},
	{"l1" : "hit", "addr" : "a2"},
	{"l1" : "hit", "addr" : "a3"},
	{"l1" : "hit", "addr" : "a4" }
	, {"l1" : "miss", "addr" : "y" } 
]

template = [
	{"l1" : "miss", "addr" : "a1", "remvd" : "x" },
	{"l1" : "any", "addr" : "a2" },
	{"l1" : "any", "addr" : "a3" },
	{"l1" : "any", "addr" : "a2" },
	{"l1" : "any", "addr" : "a3" },
	{"l1" : "any", "addr" : "a2" },
	{"l1" : "any", "addr" : "a3" },
	{"l1" : "miss", "addr" : "a4", "remvd" : "x" },
	{"l1" : "miss", "addr" : "a5", "remvd" : "x1"  }
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
	
