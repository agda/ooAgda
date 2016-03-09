class CounterCell<A> implements StatsCell<A> {

  Cell<A> cell;
  int ngets, nputs;

  CounterCell (Cell<A> c, int g, int p) {
    cell  = c;
    ngets = g;
    nputs = p;
  }

  public A get() {
    ngets++;
    return cell.get();
  }

  public void put (A s) {
    nputs++;
    cell.put(s);
  }

  public void stats() {
    System.out.println ("Counted "
      + ngets + " calls to get and "
      + nputs + " calls to put.");
  }

  public static void program (String arg) {
    CounterCell<String> c = new CounterCell(new SimpleCell("Start"), 0, 0);
    String s = c.get();
    System.out.println(s);
    c.put(arg);
    s = c.get();
    System.out.println(s);
    c.put("Over!");
    c.stats();
    return;
  }

  public static void main (String[] args) {
    program ("Hello");
  }
}
