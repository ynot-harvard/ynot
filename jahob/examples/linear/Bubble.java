class Bubble {

    private static int[] a;
    private static int n;

    public static void sort() {
        int tmp, i, j;
        n = 100;
        a = new int[n];
        i = 0;
        while /*: inv "0 <= i & i < n" */
            (i < n-1) {
            j = 0;
            while /*: inv "0 <= j & j < n-i" */
                (j<n-1-i) {
                if (a[j+1] < a[j]) {  /* compare the two neighbors */
                    tmp = a[j];         /* swap a[j] and a[j+1]      */
                    a[j] = a[j+1];
                    a[j+1] = tmp;
                }
                j = j + 1;
            }
            i = i + 1;
        }
    }
}
