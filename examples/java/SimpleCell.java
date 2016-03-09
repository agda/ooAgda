class SimpleCell<A> implements Cell<A> {

  A content;

  SimpleCell (A s) { content = s; }

  public void put (A s) {
    System.err.println("putting(" + s + ")");
    content = s;
  }

  public A get () {
    System.err.println("getting(" + content + ")");
    return content;
  }

  public static void program () {
    SimpleCell<String> c = new SimpleCell<String>("Start");
    String s = System.console().readLine();
    if (s == null) return; else {
      c.put(s);
      s = c.get();
      System.out.println(s);
      program();
    }
  }

  public static void main (String[] args) {
    program();
  }
}
