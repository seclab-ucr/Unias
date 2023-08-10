llvm_map_components_to_libnames(llvm_libs bitwriter core ipo irreader instcombine instrumentation target linker analysis scalaropts support )

file(GLOB UNIAS_SRCS
    "include/*"
    "mlta/*"
)

macro(setupEnv target)
target_include_directories(${target} PUBLIC include/ mlta/)
target_link_libraries(${target} ${SVF_LIB} ${LLVMCudd} ${llvm_libs} )
set_target_properties(${target} PROPERTIES
    RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
set_target_properties(${target} PROPERTIES
	COMPILE_FLAGS "-fno-rtti -fPIC"
)
endmacro(setupEnv)

add_executable(UniasAnalysis
    UniasAnalysis.cpp
    ${UNIAS_SRCS}
)
setupEnv(UniasAnalysis)

add_executable(Steensgaard
    Steensgaard.cpp
    ${UNIAS_SRCS}
)
setupEnv(Steensgaard)
