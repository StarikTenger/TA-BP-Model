# Set the minimum version of CMake that can be used
# To find the cmake version run
# $ cmake --version
cmake_minimum_required(VERSION 3.5)

set (CMAKE_CXX_STANDARD 20)

# Set the project name
project (pipeline_model)

# Create a sources variable with a link to all cpp files to compile
set(SOURCES
    src/PipelineState.cpp
    src/Prog.cpp
    src/TraceDiagonal.cpp
    src/Util.cpp
    src/EventTable.cpp
)

set(TARGETS
    exec_prog
    exhaustive_search
    random_search
    compare_traces
    event_table
)
foreach(TARGET ${TARGETS})
    # Add an executable for each target using the sources and the target-specific cpp file
    add_executable(${TARGET} ${SOURCES} targets/${TARGET}.cpp)

    # Set the directories that should be included in the build command for this target
    target_include_directories(${TARGET}
        PRIVATE 
            ${PROJECT_SOURCE_DIR}/include
    )
endforeach()