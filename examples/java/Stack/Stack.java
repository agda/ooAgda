public interface  Stack<E> {
  void push(E e);

  /** @throws EmptyStackException if the stack is empty **/
  E pop() throws java.util.EmptyStackException;
}
