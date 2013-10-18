// quick test of null comparison behavior in java

class NullVsNull {
  public static void main(String[] args) {
    if (null == null) {
      System.out.println("null == null");
    }
    if (null != null) {
      System.out.println("null != null");
    }
  }
}
/* output:
null == null
*/
