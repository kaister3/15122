int binsearch(int x, int[] A, int n)
{
    //@requires 0 <= n && n <= \length(A);
    //@requires is_sorted(A, 0, n);
    /*@ensures (-1 == \result && !is_in(x, A, 0, n)) || ((0 <= \result && \result < n) && A[\result] == x);@*/
    int lower = 0;
    int upper = 0;
    while (lower < upper)
    //@loop_invariant 0 <= lower && upper && upper <= n;
    //@loop_invariant (lower == 0 || A[lower-1] < x);
    //@loop_invariant (upper == n || A[upper] > x);
    {
        int middle = (lower + upper) / 2;
        //@assert lower <= middle && middle < upper;
        if (A[middle] == x)
        {
            return middle;
        }
        else if (A[middle] < x)
        {
            lower = middle + 1;
        }
        else
        {
            /*@assert(A[middle] > x@*/
            upper = middle;
        }
        
    }
    return -1;
}