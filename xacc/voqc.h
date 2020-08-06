// !!! IMPORTANT !!! This file is *generated*. Don't modify it. 
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>
#include <gmp.h>
struct final_gates { int gates; void* type1;  };

struct tuples { struct final_gates gate; int x;  };

struct triples { struct final_gates gate1; int a; int b;  };

struct quad { struct final_gates gate2; int c; int f; int e;  };

struct gate_app1 {
  struct tuples App1; struct triples App2; struct quad App3; int ans; 
};

struct with_qubits {
  int length; struct gate_app1 contents2[250000]; int qubits; 
};

struct with_qubits* optimizer(struct with_qubits* x101);
struct with_qubits* merge_rotations(struct with_qubits* x102);
struct with_qubits* cancel_single_qubit_gates(struct with_qubits* x103);
struct with_qubits* cancel_two_qubit_gates(struct with_qubits* x104);
struct with_qubits* hadamard(struct with_qubits* x105);
struct with_qubits* not_propagation(struct with_qubits* x106);
struct with_qubits* get_gate_list(char* x107);
void write_qasm_file(char* x109, struct with_qubits* x108);
void voqc(char* x111, char* x110);
struct with_qubits* load(char* x112);
int cliff(struct with_qubits* x113);
char* t_count(struct with_qubits* x114);

