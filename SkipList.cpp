/**
***
*** Copyright  (C) 1985-2011 Intel Corporation. All rights reserved.
***
*** The information and source code contained herein is the exclusive
*** property of Intel Corporation. and may not be disclosed, examined
*** or reproduced in whole or in part without explicit written authorization
*** from the company.
***
*** ----------------------------------------------------------------------------
**/


#include "cm_rt.h"
#include "../../compiler/include/cm/cm_vm.h"

// Includes bitmap_helpers.h for bitmap file open/save/compare operations.
#include "bitmap_helpers.h"

// Include cm_rt_helpers.h to convert the integer return code returned from
// the CM runtime to a meaningful string message.
#include "cm_rt_helpers.h"

// Includes isa_helpers.h to load the ISA file generated by the CM compiler.
#include "isa_helpers.h"

#include <assert.h>
#include <iostream>
#include <fstream> // To use ifstream
#include <limits>
#include <stdio.h>
#include <random>
#include <math.h>  /* log2 */
#include <time.h>
#include <stack>

#include "SkipList.h"

using namespace std;

using namespace std;
unsigned int infinity = 1 << INFINITY_SHIFT;

void cmk_skiplist_insert(SurfaceIndex skiplist, SurfaceIndex data, SurfaceIndex idxNewNodes, unsigned int start, unsigned int end);
void cmk_skiplist_search(SurfaceIndex skiplist, SurfaceIndex data, unsigned int start, unsigned int end);

bool loadFromFile(uint32_t * data, string filename, int numKeys) {
  ifstream file(filename);
  if (!file.good())
    return false;
  int value, i = 0;
  // Read an integer at a time from the line
  while (file >> value && i < numKeys)
  {
    // Add the integers from a line to a 1D array (vector)
    data[i++] = value;
  }
  file.close();
  return true;
}

void generateRandomKeys(int numKeys, string filename) {
  std::random_device rd;     // only used once to initialise (seed) engine
  std::mt19937 rng(rd());    // random-number engine used (Mersenne-Twister in this case)
  std::uniform_int_distribution<unsigned int> uni(1, 100000000); // guaranteed unbiased

  ofstream outputFile;
  outputFile.open(filename);
  int i = 0;
  while (i < numKeys) {
    outputFile << uni(rng) << " ";
    i++;
  }

  // Close the file.
  outputFile.close();
}

void dumpSkiplist(uint32_t * dst_skiplist) {
  int count = 0;
  //UINT maski = (1 << 29) - 1;
  // UINT maski2 = (1 << 28) - 1;
  int nextOffset = 0, k = 0;
  while (nextOffset != infinity) {
#if DEBUG_MODE
    printf("%d = [ ", nextOffset);
#
    for (UINT j = 0; j < 15; j++) {
      if (dst_skiplist[nextOffset + j] == 0)
        printf(" - ");
      else {
        printf("%d ", dst_skiplist[nextOffset + j]);
      }
    }
    for (UINT j = 15; j < 16; j++) {
      printf("%d ", dst_skiplist[nextOffset + j]);

    }
    printf("|| ");
#endif


    for (UINT j = 16; j < 31; j++) {
#if DEBUG_MODE
      printf("%d ", dst_skiplist[nextOffset + j]);
#endif
      if (dst_skiplist[nextOffset + j] != 0)
        count++;
    }
#if DEBUG_MODE
    for (UINT j = 31; j < 32; j++) {
      printf("%d ", dst_skiplist[nextOffset + j]);
    }
    printf(" ]\n ");
#endif

    std::stack<int> pila;

    int nextOffset2 = dst_skiplist[nextOffset + 31];
    if (nextOffset2 != 0 && nextOffset2 % 32 == 0)
      pila.push(nextOffset2);
    while (!pila.empty()) {
      nextOffset2 = pila.top();
      pila.pop();
      if (nextOffset2 != 0) {
#if DEBUG_MODE
        printf("###%d = [ ", nextOffset2);
#endif
        for (UINT j = 0; j < 31; j++) {
#if DEBUG_MODE
          printf(" %d ", dst_skiplist[nextOffset2 + j]);
#endif
          if (j < 15 && dst_skiplist[nextOffset2 + j] != 0)
            count++;
        }
#if DEBUG_MODE
        for (UINT j = 31; j < 32; j++) {
          printf(" %d ", dst_skiplist[nextOffset2 + j]);
        }
          printf(" ]\n ");
#endif
        int nextOffset3 = dst_skiplist[nextOffset2 + 15];
        if (nextOffset3 != 0 && nextOffset3 % 32 == 0)
          pila.push(nextOffset3);
      }
    }


    nextOffset = (dst_skiplist[nextOffset]);
  }

  printf("Total inserted keys = %d\n", count);

}

void insertTest(int numKeys, int numThreads, string filename) {
  uint32_t *dst_skiplist;
  uint32_t *dst_lists;
  uint32_t *dst_reads;
  uint32_t *skiplist;
  uint32_t *data;
  uint32_t *idxNewLists;
  uint32_t skiplistSize = numKeys * 32; // worst case (very high P_VALUE): 1 list per key
  cout << "runTest " << numThreads << " " << numKeys << " " << skiplistSize << endl;

  skiplist = (uint32_t*)CM_ALIGNED_MALLOC((skiplistSize) * sizeof(uint32_t), 0x1000);
  memset(skiplist, 0, sizeof(uint32_t) * skiplistSize);
  for (int i = 0; i <= LAST_ELEM; i++)
    skiplist[i] = infinity;

  data = (uint32_t*)CM_ALIGNED_MALLOC(numKeys * sizeof(uint32_t), 0x1000);
  memset(data, 0, sizeof(uint32_t) * numKeys);

  idxNewLists = (uint32_t*)CM_ALIGNED_MALLOC(sizeof(uint32_t), 0x1000);
  memset(idxNewLists, 0, sizeof(UINT));

  dst_skiplist = (uint32_t*)CM_ALIGNED_MALLOC(skiplistSize * sizeof(uint32_t), 0x1000);
  memset(dst_skiplist, 0, sizeof(UINT) * skiplistSize);

  dst_lists = (uint32_t*)CM_ALIGNED_MALLOC(sizeof(uint32_t), 0x1000);
  memset(dst_lists, 0, sizeof(UINT));

  dst_reads = (uint32_t*)CM_ALIGNED_MALLOC(numThreads*sizeof(uint32_t), 0x1000);
  memset(dst_reads, 0, sizeof(UINT)*numThreads);

                                                // Check if exists and then open the file.
  if (!loadFromFile(data, filename, numKeys)) {
    cout << "Error reading file with keys!";
    _exit(0);
  }
#if 0
  cout << "Elements: " ;
  for (int i = 0; i < numKeys; i++) {
    cout << data[i] << " ";
  }
  cout << endl;
#endif

  // Creates a CmDevice from scratch.
  // Param device: pointer to the CmDevice object.
  // Param version: CM API version supported by the runtime library.
  CmDevice *device = nullptr;
  unsigned int version = 0;
  cm_result_check(::CreateCmDevice(device, version));
  // The file linear_walker_genx.isa is generated when the kernels in the file
  // linear_walker_genx.cpp are compiled by the CM compiler.
  // Reads in the virtual ISA from "K2tree_genx.isa" to the code
  // buffer.
  std::string isa_code = cm::util::isa::loadFile("SkipList_genx.isa");
  if (isa_code.size() == 0) {
    std::cout << "Error: empty ISA binary.\n";
    exit(1);
  }

  // Creates a CmProgram object consisting of the kernels loaded from the code
  // buffer.
  // Param isa_code.data(): Pointer to the code buffer containing the virtual
  // ISA.
  // Param isa_code.size(): Size in bytes of the code buffer containing the
  // virtual ISA.
  CmProgram *program = nullptr;
  cm_result_check(device->LoadProgram(const_cast<char*>(isa_code.data()),
    isa_code.size(),
    program));

  // Create a kernel
  CmKernel* kernel = nullptr;
  cm_result_check(device->CreateKernel(program,
    CM_KERNEL_FUNCTION(cmk_skiplist_insert),
    kernel));

  CmBuffer*  skiplistBuf = nullptr;
  cm_result_check(device->CreateBuffer(skiplistSize * sizeof(unsigned int), skiplistBuf));
  cm_result_check(skiplistBuf->WriteSurface((const unsigned char*)skiplist, nullptr));

  CmBuffer*  dataBuf = nullptr;
  cm_result_check(device->CreateBuffer(numKeys * sizeof(unsigned int), dataBuf));
  cm_result_check(dataBuf->WriteSurface((const unsigned char*)data, nullptr));

  CmBuffer*  newListsBuf = nullptr;
  uint32_t newLists = 1;
  cm_result_check(device->CreateBuffer(sizeof(unsigned int), newListsBuf));
  cm_result_check(newListsBuf->WriteSurface((const unsigned char*)&newLists, nullptr));


  //cm_result_check(kernel->SetThreadCount(numThreads));

  SurfaceIndex *index0 = nullptr;
  SurfaceIndex *index1 = nullptr;
  SurfaceIndex *index2 = nullptr;
  cm_result_check(skiplistBuf->GetIndex(index0));
  cm_result_check(dataBuf->GetIndex(index1));
  cm_result_check(newListsBuf->GetIndex(index2));
  cm_result_check(kernel->SetKernelArg(0, sizeof(SurfaceIndex), index0));
  cm_result_check(kernel->SetKernelArg(1, sizeof(SurfaceIndex), index1));
  cm_result_check(kernel->SetKernelArg(2, sizeof(SurfaceIndex), index2));
  unsigned data_chunk = (numKeys) / numThreads;
  cm_result_check(kernel->SetKernelArg(3, sizeof(data_chunk), &data_chunk));


  //device->InitPrintBuffer();

  // Creates a thread space
  CmThreadSpace *thread_space = nullptr;
  cm_result_check(device->CreateThreadSpace(numThreads, 1, thread_space));

  // Create a task queue
  CmQueue* pCmQueue = NULL;
  cm_result_check(device->CreateQueue(pCmQueue));

  CmTask *pKernelArray = NULL;
  cm_result_check(device->CreateTask(pKernelArray));
  cm_result_check(pKernelArray->AddKernel(kernel));

  clock_t start = clock();
  unsigned long timeout = -1;

  CmEvent* e = NULL;
  cm_result_check(pCmQueue->Enqueue(pKernelArray, e, thread_space));
  cm_result_check(e->WaitForTaskFinished(timeout));
  clock_t end = clock(); // end timer


  cm_result_check(device->DestroyTask(pKernelArray));

  cm_result_check(skiplistBuf->ReadSurface((unsigned char *)dst_skiplist, e));
  cm_result_check(newListsBuf->ReadSurface((unsigned char *)dst_lists, e));

  cout << "# lists used = " << *dst_lists << " (" << *dst_lists*32 << ")" << endl;

  uint64_t executionTime = 0;
  cm_result_check(e->GetExecutionTime(executionTime));
  cout << "Kernel time <Insertion>" << (executionTime / 1000000) << "ms" << endl;
  cout << "Program time <Insertion> " << (end - start) << "ms" << endl;

  dumpSkiplist(dst_skiplist);
  //cm_result_check(::DestroyCmDevice(device));
  //device->FlushPrintBuffer();
  cm_result_check(device->DestroyThreadSpace(thread_space));
  cm_result_check(::DestroyCmDevice(device));

#if 1
  // ==============   search    =====================
  CmDevice *device2 = nullptr;
  cm_result_check(::CreateCmDevice(device2, version));

  CmProgram *program2 = nullptr;
  cm_result_check(device2->LoadProgram(const_cast<char*>(isa_code.data()),
    isa_code.size(),
    program2));

  CmKernel* kernel_search = nullptr;
  cm_result_check(device2->CreateKernel(program2,
    CM_KERNEL_FUNCTION(cmk_skiplist_search),
    kernel_search));

  CmBuffer* skiplistBuf2 = nullptr;
  cm_result_check(device2->CreateBuffer(skiplistSize * sizeof(unsigned int), skiplistBuf2));
  cm_result_check(skiplistBuf2->WriteSurface((const unsigned char*)dst_skiplist, nullptr));

  CmBuffer*  dataBuf2 = nullptr;
  cm_result_check(device2->CreateBuffer(numKeys * sizeof(unsigned int), dataBuf2));
  cm_result_check(dataBuf2->WriteSurface((const unsigned char*)data, nullptr));

  CmBuffer*  readsBuf = nullptr;
  cm_result_check(device2->CreateBuffer(numThreads*sizeof(unsigned int), readsBuf));
  cm_result_check(readsBuf->WriteSurface((const unsigned char*)dst_reads, nullptr));

  //cm_result_check(kernel_search->SetThreadCount(numThreads));

  SurfaceIndex *index0_search = nullptr;
  SurfaceIndex *index1_search = nullptr;
  SurfaceIndex *index2_search = nullptr;
  cm_result_check(skiplistBuf2->GetIndex(index0_search));
  cm_result_check(dataBuf2->GetIndex(index1_search));
  cm_result_check(readsBuf->GetIndex(index2_search));
  cm_result_check(kernel_search->SetKernelArg(0, sizeof(SurfaceIndex), index0_search));
  cm_result_check(kernel_search->SetKernelArg(1, sizeof(SurfaceIndex), index1_search));
  cm_result_check(kernel_search->SetKernelArg(2, sizeof(SurfaceIndex), index2_search));
  cm_result_check(kernel_search->SetKernelArg(3, sizeof(data_chunk), &data_chunk));
  //device->InitPrintBuffer();

  // Create a task queue
  CmThreadSpace *thread_space2 = nullptr;
  cm_result_check(device2->CreateThreadSpace(numThreads, 1, thread_space2));
  CmQueue* pCmQueue2 = nullptr;
  cm_result_check(device2->CreateQueue(pCmQueue2));
  CmTask *task_search = nullptr;
  cm_result_check(device2->CreateTask(task_search));
  cm_result_check(task_search->AddKernel(kernel_search));

  device2->InitPrintBuffer();

  start = clock();
  CmEvent* e2 = nullptr;
  cm_result_check(pCmQueue2->Enqueue(task_search, e2, thread_space2));
  cm_result_check(e2->WaitForTaskFinished(timeout));
  end = clock(); // end timer

  cm_result_check(e2->GetExecutionTime(executionTime));
  std::cout << "Kernel time <Search> " << (executionTime / 1000000) << "ms" << endl;
  std::cout << "Program time <Search> " << (end - start) << "ms" << endl;

  cm_result_check(readsBuf->ReadSurface((unsigned char *)dst_reads, e2));
  int tot = 0;
  for (int i = 0; i < numThreads; i++) {
    //printf("%d, ", dst_reads[i]);
    tot += dst_reads[i];
  }

  printf("\nTotal keys found %d\n", tot);


  cm_result_check(device2->DestroyTask(task_search));
  cm_result_check(device2->DestroyThreadSpace(thread_space2));
  //device2->FlushPrintBuffer();
  cm_result_check(::DestroyCmDevice(device2));


#endif

#if 0
    // generate output file
  std::string fn("skiplist_100k_p50.txt");
  ofstream myfile(fn);
  if (myfile.is_open())
  {
    for (UINT i = 0; i < skiplistSize; i++) {
      myfile << dst_skiplist[i] << " ";
    }

    myfile.close();
  }
  else printf("Unable to open file\n");
#endif

  CM_ALIGNED_FREE(skiplist);
  CM_ALIGNED_FREE(data);
  CM_ALIGNED_FREE(dst_skiplist);
  CM_ALIGNED_FREE(idxNewLists);
}


void searchTest(int numKeys, int numThreads, std::string skiplistFilename, std::string keysFilename){


  uint32_t *skiplist;
  uint32_t *data;
  uint32_t skiplistSize = numKeys * 32;
  uint32_t *dst_reads;

  skiplist = (uint32_t*)CM_ALIGNED_MALLOC(skiplistSize * sizeof(uint32_t), 0x1000);
  memset(skiplist, 0, sizeof(uint32_t) * skiplistSize);
  if (!loadFromFile(skiplist, skiplistFilename, skiplistSize)) {
    cout << "Error reading skiplist!";
    _exit(0);
  }
 
  data = (uint32_t*)CM_ALIGNED_MALLOC(numKeys * sizeof(uint32_t), 0x1000);
  memset(data, 0, sizeof(uint32_t) * numKeys);
  if(!loadFromFile(data, keysFilename, numKeys)) {
    cout << "Error reading skiplist!";
    _exit(0);
  }

  dst_reads = (uint32_t*)CM_ALIGNED_MALLOC(numThreads * sizeof(uint32_t), 0x1000);
  memset(dst_reads, 0, sizeof(UINT)*numThreads);


  // Creates a CmDevice from scratch.
  // Param device: pointer to the CmDevice object.
  // Param version: CM API version supported by the runtime library.
  CmDevice *device = nullptr;
  unsigned int version = 0;
  cm_result_check(::CreateCmDevice(device, version));
  // The file linear_walker_genx.isa is generated when the kernels in the file
  // linear_walker_genx.cpp are compiled by the CM compiler.
  // Reads in the virtual ISA from "K2tree_genx.isa" to the code
  // buffer.
  std::string isa_code = cm::util::isa::loadFile("SkipList_genx.isa");
  if (isa_code.size() == 0) {
    std::cout << "Error: empty ISA binary.\n";
    exit(1);
  }

  // Creates a CmProgram object consisting of the kernels loaded from the code
  // buffer.
  // Param isa_code.data(): Pointer to the code buffer containing the virtual
  // ISA.
  // Param isa_code.size(): Size in bytes of the code buffer containing the
  // virtual ISA.
  CmProgram *program = nullptr;
  cm_result_check(device->LoadProgram(const_cast<char*>(isa_code.data()),
    isa_code.size(),
    program));

  // Create a kernel
  CmKernel* kernel = nullptr;
  cm_result_check(device->CreateKernel(program,
    CM_KERNEL_FUNCTION(cmk_skiplist_search),
    kernel));

  CmBuffer*  skiplistBuf = nullptr;
  cm_result_check(device->CreateBuffer(skiplistSize * sizeof(unsigned int), skiplistBuf));
  cm_result_check(skiplistBuf->WriteSurface((const unsigned char*)skiplist, nullptr));

  CmBuffer*  dataBuf = nullptr;
  cm_result_check(device->CreateBuffer(numKeys * sizeof(unsigned int), dataBuf));
  cm_result_check(dataBuf->WriteSurface((const unsigned char*)data, nullptr));

  CmBuffer*  readsBuf = nullptr;
  cm_result_check(device->CreateBuffer(numThreads*sizeof(unsigned int), readsBuf));
  cm_result_check(readsBuf->WriteSurface((const unsigned char*)dst_reads, nullptr));



  //cm_result_check(kernel->SetThreadCount(numThreads));

  SurfaceIndex *index0 = nullptr;
  SurfaceIndex *index1 = nullptr;
  SurfaceIndex *index2 = nullptr;
  cm_result_check(skiplistBuf->GetIndex(index0));
  cm_result_check(dataBuf->GetIndex(index1));
  cm_result_check(readsBuf->GetIndex(index2));
  cm_result_check(kernel->SetKernelArg(0, sizeof(SurfaceIndex), index0));
  cm_result_check(kernel->SetKernelArg(1, sizeof(SurfaceIndex), index1));
  cm_result_check(kernel->SetKernelArg(2, sizeof(SurfaceIndex), index2));
  unsigned data_chunk = (numKeys) / numThreads;
  cm_result_check(kernel->SetKernelArg(3, sizeof(data_chunk), &data_chunk));

  //device->InitPrintBuffer();

  CmThreadSpace *thread_space = nullptr;
  cm_result_check(device->CreateThreadSpace(numThreads, 1, thread_space));

  // Create a task queue
  CmQueue* pCmQueue = NULL;
  cm_result_check(device->CreateQueue(pCmQueue));

  CmTask *pKernelArray = NULL;
  cm_result_check(device->CreateTask(pKernelArray));
  cm_result_check(pKernelArray->AddKernel(kernel));

  clock_t start = clock();
  unsigned long timeout = -1;

  CmEvent* e = NULL;
  cm_result_check(pCmQueue->Enqueue(pKernelArray, e, thread_space));
  cm_result_check(e->WaitForTaskFinished(timeout));
  clock_t end = clock(); // end timer

  

  uint64_t executionTime = 0;
  cm_result_check(e->GetExecutionTime(executionTime));
  cout << "Kernel time <Search> " << (executionTime / 1000000) << "ms" << endl;
  cout << "Program time <Search> " << (end - start) << "ms" << endl;

  cm_result_check(readsBuf->ReadSurface((unsigned char *)dst_reads, e));
  int tot = 0;
  for (int i = 0; i < numThreads; i++) {
    //printf("%d, ", dst_reads[i]);
    tot += dst_reads[i];
  }
  cout << "Keys found " << tot << endl;
  //device->FlushPrintBuffer();
  cm_result_check(device->DestroyTask(pKernelArray));
  cm_result_check(device->DestroyThreadSpace(thread_space));
  cm_result_check(::DestroyCmDevice(device));


  CM_ALIGNED_FREE(skiplist);
  CM_ALIGNED_FREE(data);
  CM_ALIGNED_FREE(dst_reads);
}

int main(int argc, char * argv[])
{
  int numKeys = 1000000;
  int numThreads = 1000;
  string keysFilename("1m_keys.txt");
  string skiplistFilename("skiplist_1m_p50.txt");
  //generateRandomKeys(numKeys, keysFilename);
  //insertTest(numKeys, numThreads, keysFilename);
  searchTest(numKeys, numThreads, skiplistFilename, keysFilename);
}
