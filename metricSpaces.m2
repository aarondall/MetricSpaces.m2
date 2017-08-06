needsPackage ("Nauty", DebuggingMode => false),
needsPackage ("Matroids", DebuggingMode => false),
-- needs "nautyToGraphs.m2",
-- needs "goodMatroidInput.m2",

-- some background routines
nautyToGraph = method (TypicalValue => Graph)
nautyToGraph (ZZ, String) := (n, G) -> (
	R := QQ[vars(0..n-1)];
	H := stringToGraph (G,R);
	Graphs$graph (apply (H#"edges", e -> {index (e#0), index (e#1)}))
	)


allGraphsOnN = method (TypicalValue => List)
allGraphsOnN ZZ := n -> (
	L := generateGraphs (n, OnlyConnected => true);
	G := apply (L, g -> nautyToGraph (n,g));
	G)

goodMatroidInput = method (TypicalValue => List)
goodMatroidInput List := L -> (
	G := sort unique flatten L;
	n := #G;
	E := toList (0..n-1);
	if G == E then return L else
	h := hashTable apply (n, i -> G#i => i);
	apply (L, l -> apply (l, e -> h#e))
	)

-- Test if a function is a metric
isMetric = method (TypicalValue => Boolean)
isMetric (VisibleList, Function) := (L, f) -> (
	P := toList (set L ** set L);
	T := toList ((set L)^**3);
	h := hashTable apply (P, p -> p => f p);
	testDiscerning1 := p -> (h#p =!= 0 and p#0 =!= p#1) or (h#p === 0 and  p#0 === p#1);
	testSymmetry := p -> h#p == h#(reverse p);
	testTriangle := t -> f (t#0, t#1) <= f (t#0, t#2) + f (t#2, t#1);
	--all (P, p -> testDiscerning1 p)
	all (P, p -> testDiscerning1 p and testSymmetry p)
	 and
	all (T, t -> testTriangle t)
	)

MetricSpace = new Type of HashTable
metricSpace = method (TypicalValue => MetricSpace)
metricSpace (List, Function) := (E, m) -> (
	n := #E;
	h := hashTable flatten apply (n, i -> apply (n, j -> (j,i) => m (i,j)));
	new MetricSpace from  {
		symbol GroundSet => sort E,
		symbol metric => h,
		symbol cache => new CacheTable
		}
	)

metricSpace Graphs$Graph := G -> (
	--if not isConnected G then return error "Expected a connected graph" else
	D := distanceMatrix G;
	d := (i,j) -> D_(i,j);
	metricSpace (sort vertexSet G, d)
	)

--metricSpace Digraph := G -> (
--	if not isConnected graph graph G then return error "Expected a connected graph" else
--	D := distanceMatrix G;
--	metricSpace (vertexSet G, (i,j) -> D_(i,j))
--	)

isMetricGeneratingSet = method (TypicalValue => Boolean)
isMetricGeneratingSet (List, MetricSpace) := (G, M) -> (
	test := (x,y) -> if x == y then true else not all (G, g -> M#metric#(g,x) == M#metric#(g,y));
	all (keys M#metric, p -> test p)
	)

metricGeneratingSets = method (TypicalValue => Boolean)
metricGeneratingSets MetricSpace := M -> (
	if M#cache#?GeneratingSets then return M#cache#GeneratingSets else
	G := select (subsets M#GroundSet, s -> isMetricGeneratingSet (s,M));
	M#cache#GeneratingSets = G;
	G)

inclusionMinimalGeneratingSets = method (TypicalValue => Boolean)
inclusionMinimalGeneratingSets MetricSpace := M -> (
	if M#cache#?inclusionMinimalGens then return M#cache#inclusionMinimalGens else
	G := metricGeneratingSets M;
	IMG := select (G, g -> not any (G, h -> g != h and isSubset (h,g)));
	M#cache#inclusionMinimalGens = IMG;
	IMG
	)

metricDimension = method (TypicalValue => ZZ)
metricDimension MetricSpace := M -> (
	if M#cache#?Dimension then return M#cache#Dimension else
	r := min apply (metricGeneratingSets M, g -> #g);
	M#cache#Dimension = r;
	r)

weakMetricDimension = method (TypicalValue => ZZ)
weakMetricDimension MetricSpace := M -> (
	G := metricGeneratingSets M;
	inclusionMinimalGens := select (G, g -> not any (G, h -> g != h and isSubset (h,g)));
	heights := unique apply (inclusionMinimalGens, g -> #g);
	n := # heights;
	if n === 1 then heights#0 else -1
	)

metricBases = method (TypicalValue => Boolean)
metricBases MetricSpace := M -> (
	if M#cache#?MetricBases then return M#cache#MetricBases else
	r := metricDimension M;
	B := select (metricGeneratingSets M, g -> #g == r);
	M#cache#MetricBases = B;
	B
)

isMatroidal = method (TypicalValue => Boolean)
isMatroidal MetricSpace := M -> (
	isValid  matroid goodMatroidInput (metricBases M)
	)

isWeaklyMatroidal = method (TypicalValue => Boolean)
isWeaklyMatroidal MetricSpace := M -> (
	IMG := inclusionMinimalGeneratingSets M;
	weakMetricDimension M != -1 and isValid matroid goodMatroidInput IMG)

-- this needs the Poset package but is no longer useful
--complementPoset = method (TypicalValue => Poset)
--complementPoset MetricSpace := M -> (
--	n := # M#GroundSet;
--	G := metricGeneratingSets M;
--	poset (apply (G, g -> toList (set (0..n-1) - set g)), isSubset))




end

E = {0, 1, 2, 3};
m = (i,j)-> if i==j then 0 else if i == 0 or j == 0 then 2 + 1/max(i,j) else 2;
M = metricSpace (E,m);

M = metricSpace completeGraph 4
metricBases M

restart
load "metricSpaces.m2"
select (allGraphsOnN 5, g -> not isMatroidal metricSpace g)