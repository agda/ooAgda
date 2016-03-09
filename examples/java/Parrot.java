class Parrot implements Cell<String> {

  Cell<String> cell;

  Parrot (Cell<String> c) { cell = c; }

  public String get() {
    return "(" + cell.get() + ") is what parrot got";
  }
  public void put (String s) {
    cell.put("parrot puts (" + s + ")");
  }

  public static void main (String[] args) {
    Parrot c = new Parrot(new SimpleCell("Start"));
    String s = c.get();
    System.out.println(s);
    c.put(s);
    s = c.get();
    System.out.println(s);
  }
}
