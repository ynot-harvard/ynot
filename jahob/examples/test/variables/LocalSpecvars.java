class LocalSpecvars {
    int yo;

    public static void main() 
    {
        int z;
        int i = 5;
        int j = 7;
        z = 3 + 8;
        //: specvar sum :: int;
        //: vardefs "sum == i + j + yo";
        //: assert "sum = 12";
        i = i + 1;
        //: track(sum);
        i = 8;
        //: assert "sum - yo = i + j";
    }
}
