/**
 * 作业1  重写POW和f，使得当有一个溢出时产生一个错误信号，而不是默默地工作在模运算中。
 * 你可以使用声明  error("Overflow");   来标志一个溢出。
 **/
static int flag = false;
void error(char *str) {
    flag = true;
    printf("%s!\n", str);
}

int POW(int x, int y) {
    //@requires y >= 0
    if (y == 0) {
        return 1;
    }
    else {
        unsigned long long BeforePow = (unsigned long long) POW(x, y - 1);
        unsigned long long AfterPow = (unsigned long long) x * POW(x, y - 1);
        if (AfterPow == BeforePow) {
            return x * POW(x, y - 1);
        }
        else error("Overflow");
        //@assert falg == false
    }
}

int f (int x, int y) {
    //@requires y >= 0
    //@ensures \result == POW(x, y);
    flag = 0;
    int r = 1;
    int b = x;//base
    int e = y;//exponent
    while (e > 0)
    //@loop_invariant e >= 0;
    //@loop_incvariant r * POW(b, e) == POW(x, y);
    {
       if (e % 2 == 1)
       {
           b = b * b;
           e = e / 2;
       }
    }
   //assert e = 0;
   return r; 
}

/**
 * 作业2  为f找到一个输入，使得循环不变量不满足第一个猜测：
 * @loop_invariant r * POW(b,e) == POW(x,y);
 * 修改之前的那个f函数的版
 **/

int f (int x, int y)
{
    int r = 1;
    int b = x;
    int e = y;
    while (e > 1)
    //@loop_invariant r * POW(b, e) == POW(x, y)
    {
        if (e % 2 == 1)
        {
            r = b * r;
        }
        b = b * b;
        e = e / 2; 
    }
    return r * b;
}