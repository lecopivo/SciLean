cmake_minimum_required(VERSION 3.0)
project(myproject)
 
find_package(Eigen3 3.3 REQUIRED NO_MODULE)

set(CMAKE_POSITION_INDEPENDENT_CODE ON)
 
add_library(EigenLeanCppStatic STATIC LDLT.cpp SparseMatrix.cpp)
add_library(EigenLeanCpp SHARED LDLT.cpp SparseMatrix.cpp)
target_link_libraries(EigenLeanCppStatic Eigen3::Eigen)
target_link_libraries(EigenLeanCpp Eigen3::Eigen)


