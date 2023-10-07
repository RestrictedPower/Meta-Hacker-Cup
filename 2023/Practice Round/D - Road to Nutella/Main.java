import java.util.*;
import java.util.Map.Entry;
import java.io.*;
import java.util.Arrays;
import java.util.Random;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
/*
    Solution Created: 16:50:27 07/10/2023
    Custom Competitive programming helper.
*/

public class Main {

  static boolean fileRead = true;

  /*
   * Solution:
   * 
   * 1) Break the graph into subgraphs separated by the bridges. By doing that the graph will be
   * turned into a tree of subgraphs connected by the bridges. We will treat each of these subgraphs
   * as a single node.
   * 3) For each subgraph, identify whether it is bipartite. If it isn't, this subgraph contains an
   * odd cycle.
   * 4) Find the closest distance from any subgraph to a subgraph that contains an odd cycle.
   * 5) To answer queries use the following method:
   * - If no subgraph contains odd cycle, return -1.
   * - Otherwise the answer is the minimum distance to an subgraph that contains an odd cycle among
   * all the nodes in the unique path between the given nodes.
   */

  static ArrayList<Integer> initialGraph[];
  static HashMap<Integer, HashSet<Integer>> tree;
  static HashMap<Integer, Integer> minDist;
  static DSU dsu;
  static boolean[] oddCycle;
  static boolean haveAtLeastOneOddCycle;
  static int[] parents;
  static TreeQueries tq;

  public static void answer() {
    int q = in.nextInt();
    long ans = 0;
    while (q-- > 0) {
      int u = dsu.find(in.nextInt() - 1), v = dsu.find(in.nextInt() - 1);
      if (!haveAtLeastOneOddCycle) {
        ans += -1;
        continue;
      }
      ans += tq.getMin(u, v);
    }
    out.println(ans);
  }

  public static class TreeQueries {
    public int n;
    public HashMap<Integer, Integer> parentConvert;
    public static ArrayList<Integer> adj[];
    public static int[] minDist;
    public static final int LOG = 20;

    int[] level;
    int[][] lca;
    int[][] minWeight;

    public TreeQueries(int[] parents, HashMap<Integer, Integer> incomingMinDist,
        HashMap<Integer, HashSet<Integer>> tree) {
      n = parents.length;
      parentConvert = new HashMap();
      minDist = new int[n];
      for (int i = 0; i < n; i++)
        parentConvert.put(parents[i], i);
      for (Entry<Integer, Integer> i : incomingMinDist.entrySet()) {
        minDist[parentConvert.get(i.getKey())] = i.getValue();
      }
      adj = new ArrayList[n];
      for (int i = 0; i < n; i++) {
        adj[i] = new ArrayList();
      }
      for (Entry<Integer, HashSet<Integer>> i : tree.entrySet()) {
        for (int j : i.getValue()) {
          adj[parentConvert.get(i.getKey())].add(parentConvert.get(j));
        }
      }
      // conversion done, processing...
      level = new int[n];
      lca = new int[n][LOG];
      minWeight = new int[n][LOG];

      for (int i = 0; i < n; i++) {
        for (int j = 0; j < LOG; j++) {
          lca[i][j] = -1;
          minWeight[i][j] = Integer.MAX_VALUE;
        }
      }

      dfs(0, -1, 0);
    }

    void dfs(int u, int p, int d) {
      lca[u][0] = p;
      level[u] = d;
      if (p != -1)
        minWeight[u][0] = Math.min(minDist[u], minDist[p]);
      for (int i = 1; i < LOG; i++) {
        if (lca[u][i - 1] != -1) {
          lca[u][i] = lca[lca[u][i - 1]][i - 1];
          minWeight[u][i] = Math.min(minWeight[u][i - 1], minWeight[lca[u][i - 1]][i - 1]);
        }
      }
      for (int v : adj[u]) {
        if (v != p)
          dfs(v, u, d + 1);
      }
    }

    public int getMin(int u, int v) {
      u = parentConvert.get(u);
      v = parentConvert.get(v);
      // conversion done
      int ans = Math.min(minDist[u], minDist[v]);
      if (level[u] > level[v]) {
        int tmp = u;
        u = v;
        v = tmp;
      }
      for (int i = LOG - 1; i >= 0; i--) {
        if (lca[v][i] != -1 && level[lca[v][i]] >= level[u]) {
          ans = Math.min(ans, minWeight[v][i]);
          v = lca[v][i];
        }
      }

      if (v == u)
        return ans;
      for (int i = LOG - 1; i >= 0; i--) {
        if (lca[v][i] != lca[u][i]) {
          ans = Math.min(ans, Math.min(minWeight[v][i], minWeight[u][i]));
          v = lca[v][i];
          u = lca[u][i];
        }
      }
      ans = Math.min(ans, Math.min(minWeight[v][0], minWeight[u][0]));
      return ans;
    }
  }

  public static void solve() {
    parseInitialGraph();
    BreakIntoTree ip = new BreakIntoTree(initialGraph);
    tree = ip.tree;
    dsu = ip.ds;
    oddCycle = ip.oddCycle;
    parents = ip.parents;
    haveAtLeastOneOddCycle = false;
    for (boolean i : oddCycle)
      haveAtLeastOneOddCycle |= i;
    if (haveAtLeastOneOddCycle) {
      minDist = new HashMap();
      Queue<Integer> q = new LinkedList();
      for (int i = 0; i < oddCycle.length; i++)
        if (oddCycle[i]) {
          q.add(parents[i]);
          minDist.put(parents[i], 0);
        }
      while (!q.isEmpty()) {
        int i = q.poll();
        int d = minDist.get(i);
        for (int j : tree.get(i)) {
          if (minDist.containsKey(j))
            continue;
          q.add(j);
          minDist.put(j, d + 1);
        }
      }
      tq = new TreeQueries(parents, minDist, tree);
    }
    answer();
  }

  public static class BreakIntoTree {
    private int n;
    private HashMap<Integer, HashSet<Integer>> tree;
    public DSU ds;
    public boolean[] oddCycle;
    public int[] parents;

    public BreakIntoTree(ArrayList<Integer> adj[]) {
      n = adj.length;
      ds = new DSU(n);
      HashSet<String> bridges = new Bridges(adj).findBridges();
      ArrayList<Integer> disconnectedGraph[] = new ArrayList[n];
      for (int i = 0; i < n; i++)
        disconnectedGraph[i] = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        for (int j : adj[i]) {
          int tI = i, tJ = j;
          if (tI > tJ) {
            int tmp = tI;
            tI = tJ;
            tJ = tmp;
          }
          if (bridges.contains(tI + ":" + tJ)) {
            continue;
          }
          ds.union(i, j);
          disconnectedGraph[i].add(j);
        }
      }
      HashSet<Integer> parentsH = new HashSet();
      for (int i = 0; i < n; i++)
        parentsH.add(ds.find(i));
      parents = new int[parentsH.size()];
      int idx = 0;
      for (int i : parentsH)
        parents[idx++] = i;
      BipartiteColoring bp = new BipartiteColoring(disconnectedGraph, parents, ds);
      oddCycle = bp.getOddCycle();
      tree = new HashMap();
      for (int i = 0; i < parents.length; i++)
        tree.put(parents[i], new HashSet<>());
      for (String e : bridges) {
        int l = ds.find(Integer.parseInt(e.split(":")[0])), r = ds.find(Integer.parseInt(e.split(":")[1]));
        tree.get(l).add(r);
        tree.get(r).add(l);
      }
    }
  }

  public static void parseInitialGraph() {
    int n = in.nextInt();
    int m = in.nextInt();
    initialGraph = new ArrayList[n];
    for (int i = 0; i < n; i++) {
      initialGraph[i] = new ArrayList();
    }
    for (int i = 0; i < m; i++) {
      int u = in.nextInt() - 1, v = in.nextInt() - 1;
      initialGraph[u].add(v);
      initialGraph[v].add(u);
    }
  }

  static class BipartiteColoring {
    private int[] parents;
    private int n;
    private int[] col;
    private ArrayList<Integer> adj[];
    private boolean[] oddCycle;
    private DSU ds;

    public BipartiteColoring(ArrayList<Integer> adj[], int[] parents, DSU ds) {
      this.parents = parents;
      this.ds = ds;
      oddCycle = new boolean[parents.length];
      col = new int[n = adj.length];
      this.adj = adj;
      run();
    }

    public boolean[] getOddCycle() {
      return oddCycle;
    }

    public void run() {
      Arrays.fill(oddCycle, true);
      Arrays.fill(col, -1);

      for (int p : parents) {
        dfs(p, 0);
      }
      HashSet<Integer> nonBip = new HashSet();
      for (int i = 0; i < n; i++)
        for (int j : adj[i])
          if (col[i] == col[j])
            nonBip.add(ds.find(i));
      for (int i = 0; i < parents.length; i++) {
        oddCycle[i] = nonBip.contains(parents[i]);
      }
    }

    private void dfs(int i, int color) {
      if (col[i] != -1)
        return;
      col[i] = color;
      for (int j : adj[i])
        dfs(j, color ^ 1);
    }
  }

  public static class Bridges {
    static ArrayList<Integer> adj[];
    static HashSet<String> bridges;
    static int n, time;
    static int[] low, etime;

    public Bridges(ArrayList<Integer> adj[]) {
      this.adj = adj;
      n = adj.length;
      adj = new ArrayList[n];
    }

    public static void bridgeFound(int u, int v) {
      if (u > v) {
        bridgeFound(v, u);
        return;
      }
      bridges.add(u + ":" + v);
    }

    public static void dfs(int i, int p) {
      low[i] = etime[i] = time++;
      for (int to : adj[i]) {
        if (to == p)
          continue;
        if (low[to] == -1) { // if j is not visited
          dfs(to, i);
          low[i] = Math.min(low[i], low[to]);
          if (low[to] > etime[i])
            bridgeFound(i, to);
        } else
          low[i] = Math.min(low[i], etime[to]);
      }
    }

    public static HashSet<String> findBridges() {
      bridges = new HashSet();
      low = new int[n];
      etime = new int[n];
      Arrays.fill(low, -1);
      Arrays.fill(etime, -1);
      time = 0;
      for (int i = 0; i < n; i++)
        if (etime[i] == -1)
          dfs(i, -1);
      return bridges;
    }
  }

  static class DSU {
    int n;
    int[] parent;

    public DSU(int n) {
      this.n = n;
      parent = new int[n];
      for (int i = 0; i < n; i++)
        parent[i] = i;
    }

    public int find(int i) {
      if (parent[i] == i)
        return i;
      return parent[i] = find(parent[i]);
    }

    public boolean union(int i, int j) {
      int pI = find(i), pJ = find(j);
      if (pI == pJ)
        return false; // Already united
      parent[pI] = pJ;
      return true;
    }
  }

  public static void main(String[] args) {
    in = new Reader();
    out = new Writer();
    if (fileRead) {
      out = new Writer("out.txt");
      in = new Reader("in.txt");
    }
    int t = in.nextInt();
    for (int i = 1; i <= t; i++) {
      out.print("Case #" + i + ": ");
      solve();
    }
    out.exit();
  }

  static Reader in;
  static Writer out;

static class Reader {
	
	private BufferedReader br;
	private StringTokenizer st;
	
	public Reader() {
		br = new BufferedReader(new InputStreamReader(System.in));
	}
	
	public Reader(String f){
		try {
			br = new BufferedReader(new FileReader(f));
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	public int[] na(int n) {
		int[] a = new int[n];
		for (int i = 0; i < n; i++) a[i] = nextInt();
		return a;
	}

	public double[] nd(int n) {
		double[] a = new double[n];
		for (int i = 0; i < n; i++) a[i] = nextDouble();
		return a;
	}
	
	public long[] nl(int n) {
		long[] a = new long[n];
		for (int i = 0; i < n; i++) a[i] = nextLong();
		return a;
	}

	public char[] nca() {
		return next().toCharArray();
	}

	public String[] ns(int n) {
		String[] a = new String[n];
		for (int i = 0; i < n; i++) a[i] = next();
		return a;
	}

	public int nextInt() {
		ensureNext();
		return Integer.parseInt(st.nextToken());
	}

	public double nextDouble() {
		ensureNext();
		return Double.parseDouble(st.nextToken());
	}

	public Long nextLong() {
		ensureNext();
		return Long.parseLong(st.nextToken());
	}

	public String next() {
		ensureNext();
		return st.nextToken();
	}
	
	public String nextLine() {
		try {
			return br.readLine();
		} catch (Exception e) {
			e.printStackTrace();
			return null;
		}
	}
	
	private void ensureNext() {
		if (st == null || !st.hasMoreTokens()) {
			try {
				st = new StringTokenizer(br.readLine());
			} catch (IOException e) {
				e.printStackTrace();
			}
    }
  }
}

static class Util {

  private static Random random = new Random();
  private static long MOD;
  static long[] fact, inv, invFact;

  public static void initCombinatorics(int n, long mod, boolean inversesToo, boolean inverseFactorialsToo) {
    MOD = mod;
    fact = new long[n + 1];
    fact[0] = 1;
    for (int i = 1; i < n + 1; i++)
      fact[i] = (fact[i - 1] * i) % mod;

    if (inversesToo) {
      inv = new long[n + 1];
      inv[1] = 1;
      for (int i = 2; i <= n; ++i)
        inv[i] = (mod - (mod / i) * inv[(int) (mod % i)] % mod) % mod;
    }

    if (inverseFactorialsToo) {
      invFact = new long[n + 1];
      invFact[n] = Util.modInverse(fact[n], mod);
      for (int i = n - 1; i >= 0; i--) {
        if (invFact[i + 1] == -1) {
          invFact[i] = Util.modInverse(fact[i], mod);
          continue;
        }
        invFact[i] = (invFact[i + 1] * (i + 1)) % mod;
      }
    }
  }

  public static long modInverse(long a, long mod) {
    long[] gcdE = gcdExtended(a, mod);
    if (gcdE[0] != 1)
      return -1; // Inverse doesn't exist
    long x = gcdE[1];
    return (x % mod + mod) % mod;
  }

  public static long[] gcdExtended(long p, long q) {
    if (q == 0)
      return new long[] { p, 1, 0 };
    long[] vals = gcdExtended(q, p % q);
    long tmp = vals[2];
    vals[2] = vals[1] - (p / q) * vals[2];
    vals[1] = tmp;
    return vals;
  }

  public static long nCr(int n, int r) {
    if (r > n)
      return 0;
    return (((fact[n] * invFact[r]) % MOD) * invFact[n - r]) % MOD;
  }

  public static long nPr(int n, int r) {
    if (r > n)
      return 0;
    return (fact[n] * invFact[n - r]) % MOD;
  }

  public static boolean isPrime(int n) {
    if (n <= 1)
      return false;
    if (n <= 3)
      return true;
    if (n % 2 == 0 || n % 3 == 0)
      return false;
    for (int i = 5; i * i <= n; i = i + 6)
      if (n % i == 0 || n % (i + 2) == 0)
        return false;
    return true;
  }

  public static boolean[] getSieve(int n) {
    boolean[] isPrime = new boolean[n + 1];
    for (int i = 2; i <= n; i++)
      isPrime[i] = true;
    for (int i = 2; i * i <= n; i++)
      if (isPrime[i])
        for (int j = i; i * j <= n; j++)
          isPrime[i * j] = false;
    return isPrime;
  }

  static long pow(long x, long pow, long mod) {
    long res = 1;
    x = x % mod;
    if (x == 0)
      return 0;
    while (pow > 0) {
      if ((pow & 1) != 0)
        res = (res * x) % mod;
      pow >>= 1;
      x = (x * x) % mod;
    }
    return res;
  }

  public static int gcd(int a, int b) {
    int tmp = 0;
    while (b != 0) {
      tmp = b;
      b = a % b;
      a = tmp;
    }
    return a;
  }

  public static long gcd(long a, long b) {
    long tmp = 0;
    while (b != 0) {
      tmp = b;
      b = a % b;
      a = tmp;
    }
    return a;
  }

  public static int random(int min, int max) {
    return random.nextInt(max - min + 1) + min;
  }

  public static void dbg(Object... o) {
    System.out.println(Arrays.deepToString(o));
  }

  public static void reverse(int[] s, int l, int r) {
    for (int i = l; i <= (l + r) / 2; i++) {
      int tmp = s[i];
      s[i] = s[r + l - i];
      s[r + l - i] = tmp;
    }
  }

  public static void reverse(int[] s) {
    reverse(s, 0, s.length - 1);
  }

  public static void reverse(long[] s, int l, int r) {
    for (int i = l; i <= (l + r) / 2; i++) {
      long tmp = s[i];
      s[i] = s[r + l - i];
      s[r + l - i] = tmp;
    }
  }

  public static void reverse(long[] s) {
    reverse(s, 0, s.length - 1);
  }

  public static void reverse(float[] s, int l, int r) {
    for (int i = l; i <= (l + r) / 2; i++) {
      float tmp = s[i];
      s[i] = s[r + l - i];
      s[r + l - i] = tmp;
    }
  }

  public static void reverse(float[] s) {
    reverse(s, 0, s.length - 1);
  }

  public static void reverse(double[] s, int l, int r) {
    for (int i = l; i <= (l + r) / 2; i++) {
      double tmp = s[i];
      s[i] = s[r + l - i];
      s[r + l - i] = tmp;
    }
  }

  public static void reverse(double[] s) {
    reverse(s, 0, s.length - 1);
  }

  public static void reverse(char[] s, int l, int r) {
    for (int i = l; i <= (l + r) / 2; i++) {
      char tmp = s[i];
      s[i] = s[r + l - i];
      s[r + l - i] = tmp;
    }
  }

  public static void reverse(char[] s) {
    reverse(s, 0, s.length - 1);
  }

  public static <T> void reverse(T[] s, int l, int r) {
    for (int i = l; i <= (l + r) / 2; i++) {
      T tmp = s[i];
      s[i] = s[r + l - i];
      s[r + l - i] = tmp;
    }
  }

  public static <T> void reverse(T[] s) {
    reverse(s, 0, s.length - 1);
  }

  public static void shuffle(int[] s) {
    for (int i = 0; i < s.length; ++i) {
      int j = random.nextInt(i + 1);
      int t = s[i];
      s[i] = s[j];
      s[j] = t;
    }
  }

  public static void shuffle(long[] s) {
    for (int i = 0; i < s.length; ++i) {
      int j = random.nextInt(i + 1);
      long t = s[i];
      s[i] = s[j];
      s[j] = t;
    }
  }

  public static void shuffle(float[] s) {
    for (int i = 0; i < s.length; ++i) {
      int j = random.nextInt(i + 1);
      float t = s[i];
      s[i] = s[j];
      s[j] = t;
    }
  }

  public static void shuffle(double[] s) {
    for (int i = 0; i < s.length; ++i) {
      int j = random.nextInt(i + 1);
      double t = s[i];
      s[i] = s[j];
      s[j] = t;
    }
  }

  public static void shuffle(char[] s) {
    for (int i = 0; i < s.length; ++i) {
      int j = random.nextInt(i + 1);
      char t = s[i];
      s[i] = s[j];
      s[j] = t;
    }
  }

  public static <T> void shuffle(T[] s) {
    for (int i = 0; i < s.length; ++i) {
      int j = random.nextInt(i + 1);
      T t = s[i];
      s[i] = s[j];
      s[j] = t;
    }
  }

  public static void sortArray(int[] a) {
    shuffle(a);
    Arrays.sort(a);
  }

  public static void sortArray(long[] a) {
    shuffle(a);
    Arrays.sort(a);
  }

  public static void sortArray(float[] a) {
    shuffle(a);
    Arrays.sort(a);
  }

  public static void sortArray(double[] a) {
    shuffle(a);
    Arrays.sort(a);
  }

  public static void sortArray(char[] a) {
    shuffle(a);
    Arrays.sort(a);
  }

  public static <T extends Comparable<T>> void sortArray(T[] a) {
    Arrays.sort(a);
  }

  public static int[][] rotate90(int[][] a) {
    int n = a.length, m = a[0].length;
    int[][] ans = new int[m][n];
    for (int i = 0; i < n; i++)
      for (int j = 0; j < m; j++)
        ans[m - j - 1][i] = a[i][j];
    return ans;
  }

  public static char[][] rotate90(char[][] a) {
    int n = a.length, m = a[0].length;
    char[][] ans = new char[m][n];
    for (int i = 0; i < n; i++)
      for (int j = 0; j < m; j++)
        ans[m - j - 1][i] = a[i][j];
    return ans;
  }

  public static boolean nextPermutation(int[] a) {
    int n = a.length;
    int lastIncreasing = -1;
    for (int i = n - 2; i >= 0 && lastIncreasing == -1; i--)
      if (a[i] < a[i + 1])
        lastIncreasing = i;
    if (lastIncreasing == -1)
      return false;
    int l = lastIncreasing + 1, r = n - 1;
    int lastLargestIdx = -1;
    for (int i = n - 1; i >= 0 && lastLargestIdx == -1; i--)
      if (a[lastIncreasing] < a[i])
        lastLargestIdx = i;
    int tmp = a[lastIncreasing];
    a[lastIncreasing] = a[lastLargestIdx];
    a[lastLargestIdx] = tmp;
    while (l <= r) {
      tmp = a[l];
      a[l++] = a[r];
      a[r--] = tmp;
    }
    return true;
  }
}

static class Writer {

  private PrintWriter pw;

  public Writer() {
    pw = new PrintWriter(System.out);
  }

  public Writer(String f) {
    try {
      pw = new PrintWriter(new FileWriter(f));
    } catch (IOException e) {
      e.printStackTrace();
    }
  }

  public void yesNo(boolean condition) {
    println(condition ? "YES" : "NO");
  }

  public void printArray(int[] a) {
    for (int i = 0; i < a.length; i++)
      print(a[i] + " ");
  }

  public void printlnArray(int[] a) {
    for (int i = 0; i < a.length; i++)
      print(a[i] + " ");
    pw.println();
  }

  public void printArray(long[] a) {
    for (int i = 0; i < a.length; i++)
      print(a[i] + " ");
  }

  public void printlnArray(long[] a) {
    for (int i = 0; i < a.length; i++)
      print(a[i] + " ");
    pw.println();
  }

  public void print(Object o) {
    pw.print(o.toString());
  }

  public void println(Object o) {
    pw.println(o.toString());
  }

  public void println() {
    pw.println();
  }

  public void flush() {
    pw.flush();
  }

  public void exit() {
    pw.close();
  }
}
}
