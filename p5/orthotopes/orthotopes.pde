/**
 *
 * Orthotopes (n-dimensional, rectangular arrays)
 *
 */
import java.util.Iterator;

/**
 * In geometry, an orthotope is an n-dimensional object whose edges are
 * all mutually perpendicular (like a rectangle or rectangular prism, but
 * in n dimensions).
 * 
 * Here, an orthotope (or just 'tope') is a container that acts as a multi-dimensional
 * rectangular array. (In J/APL/Nial, it would just be called an array, but that word
 * is already taken in java.)
 */
class Orthotope<T> implements Iterable<CellRef<T>> {
  // basic properties:
  final int rank; final int[] shape; final int[] stride; final int count;
  final T[] data;
  
  public Orthotope(T value, int... shape) {
    this.shape = shape;
    rank  = shape.length;
    
    // calculate strides and total count.
    // a stride is simply the distance within the flattened array between two
    // cells that are adjacent on a particular axis. This is equivalent to the
    // count of an individual item in the corresponding rank.
    //
    // For example: the innermost axis (called the x-axis by convention) 
    // consists of simple scalars, so the stride is simply 1. In a rank 2 orthotope,
    // we add the y axis, and the stride is equal to the width of one row. For
    // rank 3, we add the z axis, and the stride is equal to the width times the 
    // height of the individual rank 2 tables.
    //
    stride = new int[rank];   // one stride for each axis
    if (rank == 0) count = 1;
    else {
      stride[rank-1] = 1;       // stride for final (x) axis is always 1
      for (int i = rank - 2; i >= 0; --i) stride[i] = stride[i+1] * shape[i+1];
      // the total cell count for this tope would be the stride for the next level up,
      // (if there were one), so we calculate it the exact same way
      count = shape[0] * stride[0];
    }

    // once we know the total count, we can just create one big flat array 
    // for boring java-type system reasons, we can't actually create a
    // generic T[] directly, so instead we'll create an array of objects and cast it.
    data  = (T[]) new Object[count];
    
    // finally, fill in the value.
    for (int i = 0; i < count; ++i) data[i] = value;
  }
  
  public Iterator<CellRef<T>> iterator() {
    return new TopeWalker<T>(this);
  }

  public CellRef<T> at(int i) {
    return new CellRef<T>(this, i);
  }
}

/**
 * CellRef provides an interface to a single cell in a particular 
 * Orthotope. CellRefs are used as the loop variable when iterating through 
 * an Orthotope, so that explicit nested loops are not required.
 */
public class CellRef<T> {
  int _index; int[] _path; int[] _prev; final Orthotope<T> tope;
  
  public CellRef(Orthotope tope, int index) {
    _index = index;
    this.tope = tope;
  }
  
  int  getIndex() { return _index; }
  void setIndex(int value) {
     _index = value;
     _prev  = _path;
     _rebuildPath();
  }
  
  void _rebuildPath() {
    int tmp = _index;
    for (int i = 0; i < tope.rank; ++i) {
      _path[i] = tmp / tope.stride[i];
      tmp %= tope.stride[i];
    }
  }

  int [] path() { return _path; }
  boolean changed(int rank) { return _path[rank] == _prev[rank]; }
  int i() { return _index; }
  int x() { return _path[tope.rank-1]; }
  int y() { return _path[tope.rank-2]; }
  int z() { return _path[tope.rank-3]; }
  boolean atEnd() { return _index + 1 >= tope.count; }
}

/**
 * TopeWalker provides Iterator support for Orthotope.
 */
class TopeWalker<T> implements Iterator<CellRef<T>> {
  final CellRef<T> _cur;
  public TopeWalker(Orthotope tope) { _cur = new CellRef(tope, 0); }
  public boolean hasNext() { return ! _cur.atEnd(); }
  public CellRef<T> next() { _cur.setIndex(_cur.i() + 1); return _cur; }
  public void remove() throws UnsupportedOperationException { throw new UnsupportedOperationException(); }
}

int tests_run = 0; int tests_passed = 0;
void expect(boolean truth, String message) {
  tests_run++;
  if (truth) tests_passed++;
  else print("assertion failed: " + message + "\n");
}

void runTests() {
  
  // rank 0 tope = scalar
  Orthotope<Integer> z0 = new Orthotope<Integer>(0);
  expect(z0.rank == 0, "rank for a scalar should be 0");
  expect(z0.count == 1, "count for a scalar should be 1");
  expect(z0.shape.length == 0, "scalar shape should be []");
  
  // rank 1 tope == list/array
  Orthotope<Integer> z1 = new Orthotope<Integer>(0, 10);
  expect(z1.rank == 1, "rank should be 1");
  expect(z1.count == 10, "count should be 10");
  
  // rank 2 tope == grid/table/list of rows
  Orthotope<Integer> z2 = new Orthotope<Integer>(0, 10, 10);
  expect(z2.rank == 2, "rank should be 2");
  expect(z2.count == 100, "count should be 100, not " + z2.count);

  // rank 3 tope == volume/prism/stack of tables
  Orthotope<Integer> z3 = new Orthotope<Integer>(0, 10, 10, 10);
  expect(z3.rank == 3, "rank should be 3");
  expect(z3.count == 1000, "count should be 1000 , not " + z3.count);
  
  // rank 4
  Orthotope<Integer> z4 = new Orthotope<Integer>(0, 10, 10, 10, 10);
  expect(z4.rank == 4, "rank should be 4");
  expect(z4.count == 10000, "count should be 10000, not " + z4.count);

  print(tests_run + " tests run. " + tests_passed + " passed.");
}

void setup() {
  runTests();
}
