#include <iostream>
#include <chrono>
#include <sstream>
#include <cmath>

int main (int argc, char *argv[]) {

    int n = 1000;
    if (argc > 1) {
        std::stringstream ss(argv[1]);
        ss >> n;
    }

    double sum = 0;

    auto start = std::chrono::steady_clock::now();

    for (int i=0; i<n; i++){
        for (int j=0; j<i; j++){
            sum += sin((double)i) + cos((double)j);
        }
    }
 
    auto end = std::chrono::steady_clock::now();

    std::cout.precision(11);
    std::cout << "Computing for n := " << n << ", result := " << sum << ", method := c++ for loop, time := "
              << std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count()
              << "ms" << std::endl;

    return 0;
}
