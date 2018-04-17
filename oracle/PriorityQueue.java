package oracle;

/**
 * CSE 373, Winter 2011, Jessica Miller
 * The BinaryHeap is an -generic- implementation of the PriorityQueue interface.  
 * This is a binary min-heap implementation of the priority queue ADT.
 */
// Apdated by Yong Li 
import java.util.Arrays;
import java.util.Comparator;

public class PriorityQueue {
    
	private int[] array;
	private int[] indices;
    private int size;
    private Comparator<Integer> comparator;

    public PriorityQueue (int capacity, Comparator<Integer> comparator) {
        array = new int[capacity + 1];  
        indices = new int[capacity + 1];
        size = 0;
        this.comparator = comparator;
    }
    
    
    /**
     * Adds a value to the min-heap.
     */
    public void add(int value) {
        // grow array if needed
        if (size >= array.length - 1) {
            array = Arrays.copyOf(array, array.length * 2);
            indices = Arrays.copyOf(indices, indices.length * 2);
        }        
        
        // place element into heap at bottom
        size++;
        int index = size;
        array[index] = value;
        indices[value] = index;
        
        bubbleUp();
    }
    
    
    /**
     * Returns true if the heap has no elements; false otherwise.
     */
    public boolean isEmpty() {
        return size == 0;
    }

    
    /**
     * Returns (but does not remove) the minimum element in the heap.
     */
    public int peek() {
        if (this.isEmpty()) {
            throw new IllegalStateException();
        }
        
        return array[1];
    }

    
    /**
     * Removes and returns the minimum element in the heap.
     */
    public int remove() {
    	// what do want return?
    	int result = peek();
    	
    	// get rid of the last leaf/decrement
    	array[1] = array[size];
    	array[size] = -1;
    	size--;
    	if(size >= 1) indices[array[1]] = 1; // change indices
    	bubbleDownIndex(1);
    	
    	return result;
    }
    
    
    /**
     * Returns a String representation of BinaryHeap with values stored with 
     * heap structure and order properties.
     */
    public String toString() {
        return Arrays.toString(array);
    }

    
    /**
     * Performs the "bubble down" operation to place the element that is at the 
     * root of the heap in its correct place so that the heap maintains the 
     * min-heap order property.
     */
    private void bubbleDownIndex(int index) {
        
        // bubble down
        while (hasLeftChild(index)) {
            // which of my children is smaller?
            int smallerChild = leftIndex(index);
            
            // bubble with the smaller child, if I have a smaller child
            if (hasRightChild(index)
                && comparator.compare(array[leftIndex(index)], array[rightIndex(index)]) > 0) {
                smallerChild = rightIndex(index);
            } 
            
            if (comparator.compare(array[index], array[smallerChild]) > 0) {
                swap(index, smallerChild);
            } else {
                // otherwise, get outta here!
                break;
            }
            
            // make sure to update loop counter/index of where last el is put
            index = smallerChild;
        }        
    }
    
    public void bubbleDownValue(int value) {
    	bubbleDownIndex(indices[value]);
    }
    
    
    /**
     * Performs the "bubble up" operation to place a newly inserted element 
     * (i.e. the element that is at the size index) in its correct place so 
     * that the heap maintains the min-heap order property.
     */
    private void bubbleUp() {
        int index = this.size;
        
        while (hasParent(index)
                && 
           (comparator.compare(parent(index), array[index]) > 0)) {
            // parent/child are out of order; swap them
            swap(index, parentIndex(index));
            index = parentIndex(index);
        }        
    }
    
    public void bubbleUpValue(int value) {
    	bubbleUpIndex(indices[value]);
    }
    
    public void bubbleUpIndex(int index) {        
        while (hasParent(index)
                && 
           (comparator.compare(parent(index), array[index]) > 0)) {
            // parent/child are out of order; swap them
            swap(index, parentIndex(index));
            index = parentIndex(index);
        }        
    }
    
    
    private boolean hasParent(int i) {
        return i > 1;
    }
    
    
    private int leftIndex(int i) {
        return i * 2;
    }
    
    
    private int rightIndex(int i) {
        return i * 2 + 1;
    }
    
    
    private boolean hasLeftChild(int i) {
        return leftIndex(i) <= size;
    }
    
    
    private boolean hasRightChild(int i) {
        return rightIndex(i) <= size;
    }
    
    
    private int parent(int i) {
        return array[parentIndex(i)];
    }
    
    
    private int parentIndex(int i) {
        return i / 2;
    }
    
    // swap two elements
    private void swap(int index1, int index2) {
        int tmp = array[index1];
        array[index1] = array[index2];
        array[index2] = tmp;
        indices[array[index1]] = index1;
        indices[array[index2]] = index2;
    }
    
//    public static void main(String []args) {
//    	int[] depth = {1, 1, 0};
//    	Comparator<Integer> comparator = new ComparatorImpl(depth);
//    	
//    	PriorityQueue Q = new PriorityQueue(3, comparator);
//    	for(int i = 0; i < 3; i ++) {
//    		Q.add(i);
//    	}
//    	System.out.println(Q.toString());
//    	depth[2] = 3;
//    	Q.bubbleDownValue(2);
//    	System.out.println(Q.toString());
//    	depth[1] = 6;
//    	Q.bubbleDownValue(1);
//    	System.out.println(Q.toString());
//    }
    

}
