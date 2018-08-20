
#include <cm/cm.h>
#include "Skiplist.h"

/**
* Skip List implementation based on fixed list size.
* This corresponds to an adaptation of William Pugh's paper:
* https://dl.acm.org/citation.cfm?id=78977
*
* The list size and the cell indices can be updated based on
* the number of keys to be inserted.
* It guarantees O(logn) for all its operations (search, insert, delete).
*
*  Schema:
*
*        [  ]-------------------------------------------------->[  ]
*        [  ]---------------------------->[  ]----------------->[  ]
*        [  ]---------------------------->[  ]----------------->[  ]
*        [  ]------>[  ]----------------->[  ]----------------->[  ]
*        [  ]------>[  ]----------------->[  ]------>[  ]------>[  ]
*        [  ]------>[  ]------>[  ]------>[  ]------>[  ]------>[  ]
*        [  ]------>[  ]------>[  ]------>[  ]------>[  ]------>[  ]
*        [15]       [28]       [43]       [48]       [67]       [  ]
*        [18]       [33]       [44]       [57]       [69]       [  ]
*        [22]       [34]       [45]       [  ]       [75]       [  ]
*        [  ]       [40]       [  ]       [  ]       [  ]       [  ]
*        [  ]       [  ]       [  ]       [  ]       [  ]       [  ]
*                                                             +infinity
*
*
**/

/**
* Current setup:
*   - List size: 32 dwords
*   - Number of levels = 17
*   - Number of keys: 14
*
**/

static const uint INFINITY = (1 << INFINITY_SHIFT);
static const uint OFFSET_SHIFT = (1 << MARK_SHIFT);
static const uint OFFSET_MASK = (1 << MARK_SHIFT) - 1;

// offset for SIMD atomic operations
static const ushort CHUNK_OFFSET[16] = { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15 };
static const ushort CHUNK_ELEMENTS[32] = { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31 };

// Stack structure used for keeping track of search path
// TODO: resize vector if it becomes full
inline _GENX_ int push(vector_ref<uint, STACK_SZ> stack, uint elem) {
  if (stack[0] != STACK_SZ - 1) {
    // not full
    stack[0]++;
    stack[stack[0]] = elem;
    return 1;
  }
  else {
    // throw exception
#if DEBUG_MODE
    printf("stack full!!\n");
#endif
    return 0;
  }
}

inline _GENX_ int pop(vector_ref<uint, STACK_SZ> stack) {
  if (stack[0] != 0) {
    uint elem = stack[stack[0]];
    stack[0]--;
    return elem;
  }
  else // no elements
    return -1;
}

inline _GENX_ int top(vector_ref<uint, STACK_SZ> stack) {
  if (stack[0] != 0) {
    return stack[stack[0]];
  }
  else // no elements
    return -1;
}

// Values used by random generation function
unsigned short lfsr = 0xACE1u;
// Random generator function
inline _GENX_ uint rand() {
  
  unsigned bit = ((lfsr >> 0) ^ (lfsr >> 2) ^ (lfsr >> 3) ^ (lfsr >> 5)) & 1;
  return lfsr = (lfsr >> 1) | (bit << 15);
  /*
  vector<uint, 4> lfsr = cm_rdtsc<uint>();
  unsigned bit = ((lfsr[0] >> 0) ^ (lfsr[0] >> 2) ^ (lfsr[0] >> 3) ^ (lfsr[0] >> 5)) & 1;
  return lfsr[0] = (lfsr[0] >> 1) | (bit << 15);
  */
}

/**
*
* Generates number [LAST_LEVEL, FIRST_LEVEL] for level assignment
* every time there is an insertion.
*
**/
inline _GENX_ ushort randomLevel() {
  ushort level = 0; // start at first level
  while (rand() % 100 < P_VALUE && level < MAX_LEVEL) {
    level++;
  }
  return level;
}

/**
*
* Obtains an new offset for new list allocation in the buffer.
*
**/
inline _GENX_ uint allocateNewList(SurfaceIndex idxNewNodes, uint size) {
  vector<uint, 1> ret, offset = 0, src0 = size;
  write_atomic<ATOMIC_ADD, uint>(idxNewNodes, offset, src0, src0, ret);
  return ret[0] * CHUNK_SZ;
}


/**
*
* Searches for a key in the Skip List.
*
**/

_GENX_ bool search(SurfaceIndex skiplist, uint key) {
  vector<uint, LIST_SZ> currentList;
  vector<uint, CHUNK_SZ> followingOffsets, followingOffsets2, src1, followingKeys, keys;
  vector<ushort, CHUNK_SZ> linksMask, keysMask;
  uint nextChunkKeys, currentOffset = 0, rightPos, extraChunk = 1;

restart:


  if (extraChunk) {
    read(skiplist, (currentOffset + LIST_SZ) * 4, followingOffsets);
    followingOffsets2 = followingOffsets;
    followingOffsets &= OFFSET_MASK;

    linksMask = (followingOffsets == INFINITY | followingOffsets == 0);

    read(skiplist, 0, (followingOffsets + FIRST_KEY), followingKeys); // read min key of every following lists
    followingKeys.merge(0, linksMask);

    linksMask = (key >= followingKeys) & (followingKeys != 0);
    if (linksMask.any()) {
      // follow link
      rightPos = cm_pack_mask(linksMask);
      rightPos = WORD_SIZE - 1 - cm_fbh<uint>(rightPos);
      currentOffset = followingOffsets[rightPos];
      extraChunk = followingOffsets2[rightPos] >> MARK_SHIFT;
      goto restart;
    }
  }
  read(skiplist, currentOffset * 4, currentList);
  nextChunkKeys = currentList[CHUNK_SZ + NEXT_CHUNK];
  followingOffsets = currentList.select<CHUNK_SZ, 1>(FIRST_LINK);
  followingOffsets2 = followingOffsets;
  followingOffsets &= OFFSET_MASK;
  linksMask = (followingOffsets == INFINITY | followingOffsets == 0);

  read(skiplist, 0, (followingOffsets + FIRST_KEY), followingKeys); // read min key of every following lists
  followingKeys.merge(0, linksMask);
  
  linksMask = (key >= followingKeys) & (followingKeys != 0);
  if (linksMask.any()) {
    // follow link
    rightPos = cm_pack_mask(linksMask);
    rightPos = WORD_SIZE - 1 - cm_fbh<uint>(rightPos);
    currentOffset = followingOffsets[rightPos];
    extraChunk = followingOffsets2[rightPos] >> MARK_SHIFT;
    goto restart;
  }
  else {
   
    // key can be in current list
    keys = currentList.select<CHUNK_SZ, 1>(FIRST_KEY);
  next_chunk_keys:
    keysMask = (keys == key);
    if (keysMask.any()) {

      return true; // key found!
    }
    else {
      if (nextChunkKeys != 0 && nextChunkKeys % LIST_SZ == 0) {
        read(skiplist, nextChunkKeys * 4, currentList);
        if (key >= currentList[0]) { // right pos is in the next chunk continue with next chunk
          nextChunkKeys = currentList[NEXT_CHUNK];
          keys = currentList.select<CHUNK_SZ, 1>(0);
          goto next_chunk_keys;
        }
      }

    }
  }
  return false;
}



inline _GENX_ void
insertKeyAt(uint index, uint key, vector_ref<uint, ECHUNK_SZ> source, vector_ref<uint, ECHUNK_SZ> result) {
  vector<uint, 32> resultAux;
  resultAux.select<15, 1>(0) = source.select<15, 1>(0);
  resultAux[index] = key;
  resultAux.select<8, 1>(index + 1) = source.select<8, 1>(index);
  resultAux.select<8, 1>(index + 9) = source.select<8, 1>(index + 8);
  result.select<15, 1>(0) = resultAux.select<15, 1>(0);
}

inline _GENX_ void 
copyFrom(uint index1, uint index2, vector_ref<uint, 15> result, vector_ref<uint, 15> source) {
  vector<uint, 32> resultAux = 0, sourceAux = 0;
  resultAux.select<15, 1>(0) = result.select<15, 1>(0);
  sourceAux.select<15, 1>(0) = source.select<15, 1>(0);

  resultAux.select<8, 1>(index1) = sourceAux.select<8, 1>(index2);
  resultAux.select<8, 1>(index1 + 8) = sourceAux.select<8, 1>(index2 + 8);

  result.select<15, 1>(0) = resultAux.select<15, 1>(0);
}

inline _GENX_ void 
setValue(uint index1, vector_ref<uint, 15> result, uint value) {
  vector<uint, 32> resultAux = 0;
  resultAux.select<15, 1>(0) = result.select<15, 1>(0);
  resultAux.select<8, 1>(index1) = value;
  resultAux.select<8, 1>(index1 + 8) = value;
  result.select<15, 1>(0) = resultAux.select<15, 1>(0);
}


/**
*
* After inserting a new list, this functions updates previous lists' links according to new list level.
*
**/
_GENX_ bool
updateForwardLinks(SurfaceIndex skiplist, uint level, uint key, uint newListOffset, vector_ref<uint, STACK_SZ> stack, uint currentLevel) {
  vector<uint, CHUNK_SZ> src1, ret, offset, originalOffset(CHUNK_OFFSET);
  vector<uint, LIST_SZ> currentList;
  vector<uint, CHUNK_SZ> followingOffsets, temp16;
  vector<ushort, CHUNK_SZ> keysMask, linksMask, cElements;
  vector<ushort, LIST_SZ> chunkElements(CHUNK_ELEMENTS);

  uint currentOffset;
  for (; currentLevel < level; ) {
    currentOffset = pop(stack);
    if (currentOffset == -1) {
      // The end of the skip list was reached
      break;
      
    }
    if (currentLevel >= CHUNK_SZ) {
      currentOffset += LIST_SZ;
      cElements = chunkElements.select<CHUNK_SZ, 1>(16);
    }
    else {
      cElements = chunkElements.select<CHUNK_SZ, 1>(0);
    }
  restart:
    
    read(skiplist, currentOffset * 4, currentList);
    followingOffsets = currentList.select<CHUNK_SZ, 1>(FIRST_LINK);
    src1 = followingOffsets;
    followingOffsets &= OFFSET_MASK;

    linksMask = (followingOffsets == INFINITY);
    read(skiplist, 0, (followingOffsets + FIRST_KEY), temp16);
    temp16.merge(key, linksMask);
    keysMask = temp16 >= key;
    linksMask = (cElements < level) & (cElements >= currentLevel) & (followingOffsets != 0);
    linksMask &= keysMask;
    
    if ((linksMask == 0).all())
      continue;

    
    src1.merge(newListOffset, linksMask);

    offset = originalOffset + currentOffset;
    write_atomic<ATOMIC_CMPXCHG, uint>(skiplist, offset, src1, currentList.select<CHUNK_SZ, 1>(FIRST_LINK), ret);
    cm_fence();
    if ((ret.select<CHUNK_SZ, 1>(0) != currentList.select<CHUNK_SZ, 1>(FIRST_LINK)).any()) {
      goto restart;
    }
    currentLevel += cm_cbit(cm_pack_mask(linksMask));
    if (currentLevel == CHUNK_SZ)
      push(stack, currentOffset);    
  }

  
  return true;
}

/**
*
* Inserts a new key in the Skip List.
* Duplicates are not allowed.
*
**/
_GENX_ bool insert(SurfaceIndex skiplist, SurfaceIndex idxNewNodes, uint key)
{
  vector<uint, LIST_SZ> currentList; // offset is a mapping of offsets for new main list
  vector<ushort, LIST_SZ> chunkElements(CHUNK_ELEMENTS);
  vector<uint, CHUNK_SZ> linksChunk, linksChunk2, keysChunk, followingOffsets, followingOffsets2, chunk, offsets = 0, offsets2 = 0;
  vector<ushort, CHUNK_SZ> extraChunks;
  vector<ushort, CHUNK_SZ> linksMask, linksMask2, keysMask;
  vector<uint, CHUNK_SZ> followingKeys, keys;
  uint nextChunkLinks, nextChunkKeys, currentOffset = 0, currentChunkOffset;
  vector<uint, STACK_SZ> stack = 0;

  // Vectors used by atomic SIMD operations
  vector<uint, CHUNK_SZ> src1, src0, ret, offset, originalOffset(CHUNK_OFFSET);

  uint newListOffset = 0, minKey = 0, halfa = 0, extraChunk = 1;
  int level = -1;

  // Start in the root at level 0
  uint rightPos;
  if (level == -1) { // if level hasn't been assigned, assign it
    level = randomLevel();
  }

restart:
  push(stack, currentOffset); // track the search path
  if (extraChunk) {
    read(skiplist, (currentOffset + LIST_SZ) * 4, followingOffsets2);
    linksChunk2 = followingOffsets2;
    followingOffsets2 &= OFFSET_MASK;
    linksMask2 = (followingOffsets2 == INFINITY | followingOffsets2 == 0);
    read(skiplist, 0, (followingOffsets2 + FIRST_KEY), followingKeys); // read min key of every following lists
    followingKeys.merge(0, linksMask2);  
    linksMask2 = (key >= followingKeys) & (followingKeys != 0);
    if (linksMask2.any()) {
      // follow link
      rightPos = cm_pack_mask(linksMask2);
      rightPos = WORD_SIZE - 1 - cm_fbh<uint>(rightPos);
      currentOffset = followingOffsets2[rightPos];
      extraChunk = linksChunk2[rightPos] >> MARK_SHIFT;
      if (level > 0) {
        // save list's links
        linksMask2 = (chunkElements.select<CHUNK_SZ, 1>(16) < level) & (followingOffsets2 != 0);
        offsets2.merge(linksChunk2, linksMask2); // save offsets
      }
      goto restart;
    }
  }

  read(skiplist, currentOffset * 4, currentList);
  nextChunkLinks = currentList[NEXT_CHUNK];
  nextChunkKeys = currentList[CHUNK_SZ + NEXT_CHUNK];

  followingOffsets = 0;
  linksChunk = currentList.select<CHUNK_SZ, 1>(FIRST_LINK);
  followingOffsets = currentList.select<CHUNK_SZ, 1>(FIRST_LINK);
  followingOffsets2 = followingOffsets;
  followingOffsets &= OFFSET_MASK;

  linksMask = (followingOffsets == INFINITY | followingOffsets == 0);
  read(skiplist, 0, (followingOffsets + FIRST_KEY), followingKeys);
  followingKeys.merge(0, linksMask);

next_chunk_links:
  linksMask = (followingKeys != 0) & (key >= followingKeys);
  if (linksMask.any()) {
    // follow link
    rightPos = cm_pack_mask(linksMask);
    rightPos = WORD_SIZE - 1 - cm_fbh<uint>(rightPos);
    minKey = followingKeys[rightPos];
    currentOffset = followingOffsets[rightPos];
    extraChunk = followingKeys[rightPos] >> MARK_SHIFT;
    if (level > 0) {
      // save list's links
      linksMask = (chunkElements.select<CHUNK_SZ, 1>(0) < level) & (followingOffsets.select<CHUNK_SZ, 1>(0) != 0);
      offsets.merge(followingOffsets, linksMask); // save offsets
    }
    goto restart;
  }
  else {
    // last option: key can be in current range
    currentChunkOffset = currentOffset + 16;
    if (key >= minKey) {
      keysChunk = currentList.select<CHUNK_SZ, 1>(FIRST_KEY);
      keys = currentList.select<CHUNK_SZ, 1>(FIRST_KEY);
    next_chunk_keys:
      keysMask = (keys == 0) | (keys >= key);
      if (keysMask.select<15,1>(0).any()) {
        if (nextChunkKeys != 0 && nextChunkKeys % LIST_SZ == 0) {
          vector<uint, LIST_SZ> currentList2;
          read(skiplist, nextChunkKeys * 4, currentList2);
          if (key >= currentList2[0]) { // right pos is in the next chunk continue with next chunk
            currentChunkOffset = nextChunkKeys;
            nextChunkKeys = currentList2[NEXT_CHUNK];
            keys = currentList2.select<CHUNK_SZ, 1>(0);
            keysChunk = currentList2.select<CHUNK_SZ, 1>(0);
            currentList = currentList2;
            goto next_chunk_keys;
          }
        }
        // find position
        rightPos = cm_pack_mask(keysMask);
        rightPos = cm_fbl<ushort>(rightPos);
        if (keys[rightPos] == key) { // key already exists
          return false;
        }

        // insert key at this position
        if (level > 0 && rightPos != 0) {
          
          // create new list and insert key innnew List
          vector<uint, 32> forward = 0;
          if (newListOffset == 0) { // if the new list has not been allocated
            newListOffset = level > CHUNK_SZ ? allocateNewList(idxNewNodes, 3) : allocateNewList(idxNewNodes, 2); // 32 -> 64 dwords
          }
          src1 = src0 = keysChunk;
          
          forward[FIRST_KEY] = key;
          if (nextChunkKeys % LIST_SZ == 0)
            forward[CHUNK_SZ + NEXT_CHUNK] = keysChunk[NEXT_CHUNK];

          // Steal keys from previous list, if any (this includes also the 'next' pointers)
          if (keys[rightPos] != 0) {
            setValue(rightPos, src1.select<ECHUNK_SZ, 1>(0), 0);
            copyFrom(1, rightPos, forward.select<ECHUNK_SZ, 1>(FIRST_KEY), keysChunk.select<ECHUNK_SZ, 1>(0));
          }
          src1[NEXT_CHUNK] = newListOffset + CHUNK_SZ;
          // save latest list's links
          linksMask = (chunkElements.select<CHUNK_SZ, 1>(0) < level) & (followingOffsets.select<CHUNK_SZ, 1>(FIRST_LINK) != 0);
          offsets.merge(linksChunk, linksMask); // save offsets
          // Write new chunk of links
          forward.select<CHUNK_SZ, 1>(0) = offsets.select<CHUNK_SZ, 1>(0);
          write(skiplist, (newListOffset) * 4, forward);
          
          if (level > CHUNK_SZ) {
            // save latest list's links
            linksMask2 = (chunkElements.select<CHUNK_SZ, 1>(16) < level) & (followingOffsets2 != 0);
            offsets2.merge(linksChunk2, linksMask2); // save offsets
            //printf("followingoffsets2 : %d %d %d %d [] cbit %d %d \n", followingOffsets2[0], followingOffsets2[1], followingOffsets2[2], followingOffsets2[3], linksMask2[0], linksMask2[1]);
            write(skiplist, (newListOffset + LIST_SZ) * 4, offsets2);
            newListOffset |= OFFSET_SHIFT;
          }
          
          /**
          * Insertion of new list is done in two steps:
          * 1.- In the first step, the second half of currentList is updated with the link to new list
          * as well as the reflection of stolen values.
          * 2.- In second step, all the forward links of lists that are in the search path
          * of new key are updated to new key's list offset.
          *
          * SIMD16 atomic write operations are performed to guarantee synchronization. However, only
          * step one is exclusively required.
          * In step one, this SIMD16 write includes the forward offset to the new list (only 1 link) and
          * keys without the stolen ones. This is the time where an insertion is really reflected for other
          * threads.
          * Once this step one is done, can continue with step two.
          **/

          uint currentLevel = 0;
          // Perform SIMD16 CAS operation on Keys chunk with updated pointer
          offset = originalOffset + currentChunkOffset;
          write_atomic<ATOMIC_CMPXCHG, uint>(skiplist, offset, src1, src0, ret);
          cm_fence();
          if ((ret.select<CHUNK_SZ, 1>(0) != src0.select<CHUNK_SZ, 1>(0)).any()) {
            stack = 0;
            currentOffset = 0;
            extraChunk = 1;
            goto restart;
          }

          // Perform SIMD16 CAS operation on Links chunk with updated pointer
          offset = originalOffset + currentOffset;
          src1 = linksChunk;
          src0 = src1;
          currentLevel = cm_cbit(cm_pack_mask(linksMask));
          src1.merge(newListOffset, linksMask); // save offsets  
          write_atomic<ATOMIC_CMPXCHG, uint>(skiplist, offset, src1, src0, ret);
          cm_fence();
          if ((ret.select<CHUNK_SZ, 1>(0) != src0.select<CHUNK_SZ, 1>(0)).any()) {
            currentOffset = 0;
            stack = 0;
            extraChunk = 1;
            goto restart;
          }

          // Change lists' forward links of new list's offset 
          if (currentLevel < level) {
            pop(stack);
            updateForwardLinks(skiplist, level, key, newListOffset, stack, currentLevel);
          }
          return true;
        }
        else {
          // insert in current list

          if (keys[rightPos] == 0) {
            // Slot is available
            src1 = keysChunk;
            src1[rightPos] = key;
            offset = originalOffset + currentChunkOffset;
            if (nextChunkKeys != 0 && nextChunkKeys % LIST_SZ == CHUNK_SZ)
              src1(NEXT_CHUNK) = 0; // cleaning temporary link
            write_atomic<ATOMIC_CMPXCHG, uint>(skiplist, offset, src1, keysChunk, ret);
            cm_fence();
            if ((ret.select<CHUNK_SZ, 1>(0) != keysChunk.select<CHUNK_SZ, 1>(0)).any()) {
              currentOffset = 0;
              stack = 0;
              extraChunk = 1;
              goto restart;
            }
            return true;

          }
          else {
            // insert in the middle of list
            if (keysChunk[LAST_ELEM] != 0) {
              // overflow, so split current chunk
              if (newListOffset == 0) { // if the new list has not been allocated
                newListOffset = allocateNewList(idxNewNodes, 2); // 32 -> 64 dwords
              }
              chunk = 0;
              src1 = keysChunk;
              src1[NEXT_CHUNK] = newListOffset;
              chunk[0] = key;
              chunk[NEXT_CHUNK] = keysChunk[NEXT_CHUNK];
              offset = originalOffset + currentChunkOffset;
              uint i = rightPos, j = 1;
              copyFrom(j, i, chunk.select<ECHUNK_SZ, 1>(0), chunk.select<ECHUNK_SZ, 1>(0));
              setValue(i, src1.select<ECHUNK_SZ, 1>(0), 0);

              write(skiplist, (newListOffset) * 4, chunk);
              write_atomic<ATOMIC_CMPXCHG, uint>(skiplist, offset, src1, keysChunk, ret);
              cm_fence();
              if ((ret.select<CHUNK_SZ, 1>(0) != keysChunk.select<CHUNK_SZ, 1>(0)).any()) {
                currentOffset = 0;
                stack = 0;
                extraChunk = 1;
                goto restart;
              }
              return true;
            }
            else {
              //regular insertion, shift keys greater than key
              src1 = 0;
              insertKeyAt(rightPos, key, keysChunk.select<ECHUNK_SZ, 1>(0), src1.select<ECHUNK_SZ, 1>(0));
              if (nextChunkKeys != 0 && nextChunkKeys % LIST_SZ == CHUNK_SZ)
                src1[NEXT_CHUNK] = 0;
              else
                src1[NEXT_CHUNK] = keysChunk[NEXT_CHUNK];
              offset = originalOffset + currentChunkOffset;

              write_atomic<ATOMIC_CMPXCHG, uint>(skiplist, offset, src1, keysChunk, ret);
              cm_fence();
              if ((ret.select<CHUNK_SZ, 1>(0) != keysChunk.select<CHUNK_SZ, 1>(0)).any()) {
                currentOffset = 0;
                stack = 0;
                extraChunk = 1;
                goto restart;
              }
              return true;
            }
          }
        }


      }
      else {
        if (nextChunkKeys != 0 && nextChunkKeys % 32 == 0) {
          vector<uint, LIST_SZ> currentList2;
          read(skiplist, nextChunkKeys * 4, currentList2);
          if (key >= currentList2[0]) { // right pos is in the next chunk continue with next chunk
            nextChunkKeys = currentList[NEXT_CHUNK];
            currentChunkOffset = nextChunkKeys;
            nextChunkKeys = currentList2[NEXT_CHUNK];
            keys = currentList2.select<CHUNK_SZ, 1>(0);
            keysChunk = currentList2.select<CHUNK_SZ, 1>(0);
            currentList = currentList2;
            goto next_chunk_keys;
          }
          else {
            // Current chunk is full and attached chunk are all greater than key
            if (newListOffset == 0) { // if the new list has not been allocated
              newListOffset = allocateNewList(idxNewNodes, 2); // 32 
            }
            chunk = 0;
            src1 = keysChunk;
            chunk[NEXT_CHUNK] = src1[NEXT_CHUNK];
            src1[NEXT_CHUNK] = newListOffset;
            chunk[0] = key;
            offset = originalOffset + currentChunkOffset;
            write(skiplist, (newListOffset) * 4, chunk);
            write_atomic<ATOMIC_CMPXCHG, uint>(skiplist, offset, src1, keysChunk, ret);
            cm_fence();
            if ((ret.select<CHUNK_SZ, 1>(0) != keysChunk.select<CHUNK_SZ, 1>(0)).any()) {
              currentOffset = 0;
              stack = 0;
              extraChunk = 1;
              goto restart;
            }
            return true;
          }
        }
        else {
          // Current chunk is full and there is no attached chunk
          if (newListOffset == 0) { // if the new list has not been allocated
            newListOffset = allocateNewList(idxNewNodes, 2); // 32 
          }
          chunk = 0;
          src1 = keysChunk;
          src1[NEXT_CHUNK] = newListOffset;
          chunk[0] = key;
          offset = originalOffset + currentChunkOffset;
          write(skiplist, (newListOffset) * 4, chunk);
          write_atomic<ATOMIC_CMPXCHG, uint>(skiplist, offset, src1, keysChunk, ret);
          cm_fence();
          if ((ret.select<CHUNK_SZ, 1>(0) != keysChunk.select<CHUNK_SZ, 1>(0)).any()) {
            currentOffset = 0;
            stack = 0;
            extraChunk = 1;
            goto restart;
          }
          return true;
        }
      }
    }
  }
  return false;
}

/**
*
* Deletes a key in the Skip List.
*
**/
_GENX_ bool deleteKey(SurfaceIndex skiplist, uint key) {
  vector<uint, LIST_SZ> currentList;
  vector<uint, CHUNK_SZ> followingOffsets, followingKeys, keys;
  vector<ushort, CHUNK_SZ> linksMask, keysMask;
  uint nextChunkKeys, currentOffset = 0, rightPos, currentChunkOffset;

  // Vectors used by atomic SIMD operations
  vector<uint, CHUNK_SZ> src1, src0, ret, offset, originalOffset(CHUNK_OFFSET);

restart:
  read(skiplist, currentOffset * 4, currentList);
  nextChunkKeys = currentList[CHUNK_SZ + NEXT_CHUNK];
  followingOffsets = currentList.select<CHUNK_SZ, 1>(FIRST_LINK);
  linksMask = (followingOffsets == INFINITY | followingOffsets == 0);

  read(skiplist, 0, (followingOffsets + FIRST_KEY), src1); // read min key of every following lists
  src1.merge(0, linksMask);

  followingKeys = src1;

  linksMask = (key >= followingKeys) & (followingKeys != 0);
  if (linksMask.any()) {
    // follow link
    rightPos = cm_pack_mask(linksMask);
    rightPos = WORD_SIZE - 1 - cm_fbh<uint>(rightPos);
    currentOffset = followingOffsets[rightPos];
    goto restart;
  }
  else {
    currentChunkOffset = currentOffset + CHUNK_SZ;
    // key can be in current list
    keys = currentList.select<CHUNK_SZ, 1>(FIRST_KEY);
  next_chunk_keys:
    keysMask = (keys == key);
    if ((keysMask.select<ECHUNK_SZ, 1>(0)).any()) {
      uint totElems = cm_cbit(cm_pack_mask(keys != 0));
      if (totElems == 2) { // 2 means ket + pointer to next chunk
                           // It will become empty. 
                           // - Mark as delete. 
                           // - By pass from previous chunk
        rightPos = cm_pack_mask(keysMask);
        rightPos = cm_fbl<ushort>(rightPos);
        src1[rightPos] = 0;
        offset = originalOffset + currentChunkOffset;
        write_atomic<ATOMIC_CMPXCHG, uint>(skiplist, offset, src1, keys, ret);
        cm_fence();
        if ((ret.select<CHUNK_SZ, 1>(0) != keys.select<CHUNK_SZ, 1>(0)).any()) {
          currentOffset = 0;
          goto restart;
        }
        return true;
      }
      else {
        // Normal removal
        rightPos = cm_pack_mask(keysMask);
        rightPos = cm_fbl<ushort>(rightPos);
        src1 = keys;
       // copyFrom(rightPos, rightPos + 1, src1, src1); // remove key
        offset = originalOffset + currentChunkOffset;
        write_atomic<ATOMIC_CMPXCHG, uint>(skiplist, offset, src1, keys, ret);
        cm_fence();
        if ((ret.select<CHUNK_SZ, 1>(0) != keys.select<CHUNK_SZ, 1>(0)).any()) {
          currentOffset = 0;
          goto restart;
        }
        return true;
      }
    }
    else {
      if (nextChunkKeys != 0 && nextChunkKeys % LIST_SZ == 0) {
        read(skiplist, nextChunkKeys * 4, currentList);
        if (key >= currentList[0]) { // right pos is in the next chunk continue with next chunk
          currentChunkOffset = nextChunkKeys;
          nextChunkKeys = currentList[NEXT_CHUNK];
          keys = currentList.select<CHUNK_SZ, 1>(0);
          goto next_chunk_keys;
        }
      }

    }
  }
  return false;
}


_GENX_MAIN_ void cmk_skiplist_insert(SurfaceIndex skiplist, SurfaceIndex data, SurfaceIndex idxNewNodes, uint data_chunk, uint numKeys) {

  vector<uint, 32> ret;

  uint keys = 0, insertedKeys = 0;
  unsigned short thread_id = get_thread_origin_x();
  unsigned start = data_chunk * thread_id;
  unsigned end = data_chunk * thread_id + data_chunk;
  if (end > numKeys) {
    data_chunk = numKeys - start;
    end = numKeys;
  }
  for (uint i = start; i < end; i += 32) {
    read(DWALIGNED(data), i * 4, ret);
    for (uint j = 0; j < 32 && keys < data_chunk; j++, keys++) {
      if (ret[j] != 0 && insert(skiplist, idxNewNodes, ret[j])) {
        insertedKeys++;
      }
    }
  }
}

_GENX_MAIN_ void cmk_skiplist_search(SurfaceIndex skiplist, SurfaceIndex data, SurfaceIndex reads, uint data_chunk, uint numKeys) {
  vector<uint, 32> ret;

  uint keys = 0;
  vector<uint, 1> foundKeys = 0;
  unsigned short thread_id = get_thread_origin_x();
  unsigned start = data_chunk * thread_id;
  unsigned end = data_chunk * thread_id + data_chunk;
  if (end > numKeys) {
    data_chunk = numKeys - start;
    end = numKeys;
  }
  for (uint i = start; i < end; i += 32) {
    read(DWALIGNED(data), i * 4, ret);
    for (uint j = 0; j < 32 && keys < data_chunk; j++, keys++) {
      if (ret[j] != 0 && search(skiplist, ret[j])) {
        foundKeys[0]++;
      }
    }
  }
  // write number of keys successfully found
  write(reads, 0, thread_id, foundKeys[0]);
}

