struct a {
    char a;
    struct {
        int b[2][4];
    };
    double c;
};
int main() {
    struct a  temp = {
        'a',
        {{{1, 2 ,3 ,4}, {5, 6, 7, 8}}},
        0.1
    };
    return 0;
}
