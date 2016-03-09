import java.util.LinkedList;

public class StackLinkedList<T> implements Stack<T> {
   private LinkedList<T> list = new LinkedList<T>();

   public void push(T item) { list.addFirst(item); }

   public T pop() throws java.util.NoSuchElementException
   {
      if (list.isEmpty()) { throw new java.util.NoSuchElementException(); }
      else return list.removeFirst();
   }


    public static void main(String[] args) {
        StackLinkedList s = new StackLinkedList();

        String str1 = System.console().readLine();
        s.push(str1);
        String str2 = System.console().readLine();
        s.push(str2);

        System.out.println("first pop: " + s.pop());

        String str3 = System.console().readLine();
        s.push(str3);

        System.out.println("second pop: " + s.pop());

        System.out.println("third pop: " + s.pop());
        System.out.println("fourth pop: " + s.pop());
    }
}
