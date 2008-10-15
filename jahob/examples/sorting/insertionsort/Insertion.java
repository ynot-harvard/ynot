import java.util.Random;

public class Insertion
    /* 
       Performs insertion sort on an array of InsertionSortNodes.  The
       key field of the InsertionSortNode determines the order of the
       node in the array.  The value field contains the data.
    */
{

    public static void main(String[] args)
    {
	Random generator = new Random();
	
	int size = generator.nextInt(50);

	InsertionSortNode[] arr = new InsertionSortNode[size];

	int i = 0;
	
	while(i < arr.length)
	{
	    arr[i] = new InsertionSortNode();
	    arr[i].key = generator.nextInt(100);
	    i = i + 1;
	}

	printArray(arr);
	
	insertionSort(arr);

	printArray(arr);
    }
    
    public static void insertionSort(InsertionSortNode[] arr)
    /*: 
      requires "arr ~= null &
        (ALL k. (0 <= k & k < (Array.length arr)) --> arr.[k] ~= null)"
      modifies "Array.arrayState"
      ensures "arr ~= null &
        (ALL k. (0 <= k & k < (Array.length arr)) --> arr.[k] ~= null) &
        (ALL k. ((0 <= k & k < ((Array.length arr) - 1)) --> 
        (arr.[k]..InsertionSortNode.key <= arr.[k+1]..InsertionSortNode.key)))"
    */
    {
	int i = 1;

	while 
	    /*: inv "(ALL k. (0 <= k & k < (Array.length arr)) --> arr.[k] ~= null) &
		(ALL k. (0 <= k & k < (i - 1)) -->
		(arr.[k]..InsertionSortNode.key <= arr.[k+1]..InsertionSortNode.key))"
	    */
	    (i < arr.length)
	{
	    int j = i;
	    while
		/*: inv "j <= i &  
		  (ALL k. (0 <= k & k < (Array.length arr)) --> arr.[k] ~= null) &
		  (ALL k. (0 <= k & k < (j - 1)) --> 
		  (arr.[k]..InsertionSortNode.key <= arr.[k + 1]..InsertionSortNode.key)) &
		  (ALL k. (j <= k & k < i) --> 
		  (arr.[k]..InsertionSortNode.key <= arr.[k + 1]..InsertionSortNode.key)) &
		  ((0 < j & j < i) --> 
		  (arr.[j - 1]..InsertionSortNode.key <= arr.[j + 1]..InsertionSortNode.key))"
		 */
		(j > 0)
	    {
		if (arr[j].key < arr[j-1].key)
		{
		    InsertionSortNode tmp = arr[j];
		    arr[j] = arr[j-1];
		    arr[j-1] = tmp;
		}
		j = j - 1;
	    }
	    i = i + 1;
	}
    }

    public static void printArray(InsertionSortNode[] arr)
    {
	int i = 0;

	while(i < arr.length)
	{
	    System.out.print(arr[i].key + " ");
	    i = i + 1;
	}

	System.out.println("");
    }
}
