#pragma once

#define DEBUG_MODE 0
#define CHECK_ERRORS 0

#define SIMD_SZ 8
#define MAX_TS_WIDTH 1024
#define WORD_SIZE 32
#define INFINITY_SHIFT 30

// Skiplist parameters
#define P_VALUE 50 // probability for level's height assignement 
#define MAX_LEVEL 15
#define CHUNK_SZ 16
#define ECHUNK_SZ 15
#define LIST_SZ 32
#define STACK_SZ 64
// indices
#define NEXT_CHUNK 15
#define FIRST_KEY 16
#define FIRST_LINK 0
#define LAST_ELEM 14



