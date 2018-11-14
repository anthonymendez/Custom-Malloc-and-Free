/* 
 * Joshua Howell
 * jhowell@umass.edu
 * 
 * Anthony Mendez
 * anthonymende@umass.edu
 */
/*-------------------------------------------------------------------                             
 * Lab 5 Starter code:                                                                            
 *        single doubly-linked free block list with LIFO policy                                   
 *        with support for coalescing adjacent free blocks  
 *
 * Terminology:
 * o We will implement an explicit free list allocator
 * o We use "next" and "previous" to refer to blocks as ordered in
 *   the free list.
 * o We use "following" and "preceding" to refer to adjacent blocks
 *   in memory.
 *-------------------------------------------------------------------- */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* Macros for unscaled pointer arithmetic to keep other code cleaner.  
   Casting to a char* has the effect that pointer arithmetic happens at
   the byte granularity (i.e. POINTER_ADD(0x1, 1) would be 0x2).  (By
   default, incrementing a pointer in C has the effect of incrementing
   it by the size of the type to which it points (e.g. BlockInfo).)
   We cast the result to void* to force you to cast back to the 
   appropriate type and ensure you don't accidentally use the resulting
   pointer as a char* implicitly.  You are welcome to implement your
   own pointer arithmetic instead of using these macros.
*/
#define UNSCALED_POINTER_ADD(p,x) ((void*)((char*)(p) + (x)))
#define UNSCALED_POINTER_SUB(p,x) ((void*)((char*)(p) - (x)))


/******** FREE LIST IMPLEMENTATION ***********************************/


/* A BlockInfo contains information about a block, including the size
   and usage tags, as well as pointers to the next and previous blocks
   in the free list.  This is exactly the "explicit free list" structure
   illustrated in the lecture slides.
   
   Note that the next and prev pointers and the boundary tag are only
   needed when the block is free.  To achieve better utilization, mm_malloc
   should use the space for next and prev as part of the space it returns.

   +--------------+
   | sizeAndTags  |  <-  BlockInfo pointers in free list point here
   |  (header)    |
   +--------------+
   |     next     |  <-  Pointers returned by mm_malloc point here
   +--------------+
   |     prev     |
   +--------------+
   |  space and   |
   |   padding    |
   |     ...      |
   |     ...      |
   +--------------+
   | boundary tag |
   |  (footer)    |
   +--------------+
*/
struct BlockInfo {
  // Size of the block (in the high bits) and tags for whether the
  // block and its predecessor in memory are in use.  See the SIZE()
  // and TAG macros, below, for more details.
  size_t sizeAndTags;
  // Pointer to the next block in the free list.
  struct BlockInfo* next;
  // Pointer to the previous block in the free list.
  struct BlockInfo* prev;
};
typedef struct BlockInfo BlockInfo;


/* Pointer to the first BlockInfo in the free list, the list's head. 
   
   A pointer to the head of the free list in this implementation is
   always stored in the first word in the heap.  mem_heap_lo() returns
   a pointer to the first word in the heap, so we cast the result of
   mem_heap_lo() to a BlockInfo** (a pointer to a pointer to
   BlockInfo) and dereference this to get a pointer to the first
   BlockInfo in the free list. */
#define FREE_LIST_HEAD *((BlockInfo **)mem_heap_lo())

/* Size of a word on this architecture. */
#define WORD_SIZE sizeof(void*)

/* Minimum block size (to account for size header, next ptr, prev ptr,
   and boundary tag) */
#define MIN_BLOCK_SIZE (sizeof(BlockInfo) + WORD_SIZE)

/* Alignment of blocks returned by mm_malloc. */
#define ALIGNMENT 8

/* SIZE(blockInfo->sizeAndTags) extracts the size of a 'sizeAndTags' field.
   Also, calling SIZE(size) selects just the higher bits of 'size' to ensure
   that 'size' is properly aligned.  We align 'size' so we can use the low
   bits of the sizeAndTags field to tag a block as free/used, etc, like this:
   
      sizeAndTags:
      +-------------------------------------------+
      | 63 | 62 | 61 | 60 |  . . . .  | 2 | 1 | 0 |
      +-------------------------------------------+
        ^                                       ^
      high bit                               low bit

   Since ALIGNMENT == 8, we reserve the low 3 bits of sizeAndTags for tag
   bits, and we use bits 3-63 to store the size.

   Bit 0 (2^0 == 1): TAG_USED
   Bit 1 (2^1 == 2): TAG_PRECEDING_USED
*/
#define SIZE(x) ((x) & ~(ALIGNMENT - 1))

/* TAG_USED is the bit mask used in sizeAndTags to mark a block as used. */
#define TAG_USED 1 

/* TAG_PRECEDING_USED is the bit mask used in sizeAndTags to indicate
   that the block preceding it in memory is used. (used in turn for
   coalescing).  If the previous block is not used, we can learn the size
   of the previous block from its boundary tag */
#define TAG_PRECEDING_USED 2


/* Find a free block of the requested size in the free list.  Returns
   NULL if no free block is large enough. */
static void * searchFreeList(size_t reqSize) {   
  BlockInfo* freeBlock;

  freeBlock = FREE_LIST_HEAD;
  while (freeBlock != NULL){
    if (SIZE(freeBlock->sizeAndTags) >= reqSize) {
      return freeBlock;
    } else {
      freeBlock = freeBlock->next;
    }
  }
  return NULL;
}
           
/* Insert freeBlock at the head of the list.  (LIFO) */
static void insertFreeBlock(BlockInfo* freeBlock) {
  BlockInfo* oldHead = FREE_LIST_HEAD;
  freeBlock->next = oldHead;
  if (oldHead != NULL) {
    oldHead->prev = freeBlock;
  }
  //  freeBlock->prev = NULL;
  FREE_LIST_HEAD = freeBlock;
}      

/* Remove a free block from the free list. */
static void removeFreeBlock(BlockInfo* freeBlock) {
  BlockInfo *nextFree, *prevFree;
  
  nextFree = freeBlock->next;
  prevFree = freeBlock->prev;

  // If the next block is not null, patch its prev pointer.
  if (nextFree != NULL) {
    nextFree->prev = prevFree;
  }

  // If we're removing the head of the free list, set the head to be
  // the next block, otherwise patch the previous block's next pointer.
  if (freeBlock == FREE_LIST_HEAD) {
    FREE_LIST_HEAD = nextFree;
  } else {
    prevFree->next = nextFree;
  }
}

/* Coalesce 'oldBlock' with any preceeding or following free blocks. */
static void coalesceFreeBlock(BlockInfo* oldBlock) {
  BlockInfo *blockCursor;
  BlockInfo *newBlock;
  BlockInfo *freeBlock;
  // size of old block
  size_t oldSize = SIZE(oldBlock->sizeAndTags);
  // running sum to be size of final coalesced block
  size_t newSize = oldSize;

  // Coalesce with any preceding free block
  blockCursor = oldBlock;
  while ((blockCursor->sizeAndTags & TAG_PRECEDING_USED)==0) { 
    // While the block preceding this one in memory (not the
    // prev. block in the free list) is free:

    // Get the size of the previous block from its boundary tag.
    size_t size = SIZE(*((size_t*)UNSCALED_POINTER_SUB(blockCursor, WORD_SIZE)));
    // Use this size to find the block info for that block.
    freeBlock = (BlockInfo*)UNSCALED_POINTER_SUB(blockCursor, size);
    // Remove that block from free list.
    removeFreeBlock(freeBlock);

    // Count that block's size and update the current block pointer.
    newSize += size;
    blockCursor = freeBlock;
  }
  newBlock = blockCursor;

  // Coalesce with any following free block.
  // Start with the block following this one in memory
  blockCursor = (BlockInfo*)UNSCALED_POINTER_ADD(oldBlock, oldSize);
  while ((blockCursor->sizeAndTags & TAG_USED)==0) {
    // While the block is free:

    size_t size = SIZE(blockCursor->sizeAndTags);
    // Remove it from the free list.
    removeFreeBlock(blockCursor);
    // Count its size and step to the following block.
    newSize += size;
    blockCursor = (BlockInfo*)UNSCALED_POINTER_ADD(blockCursor, size);
  }
  
  // If the block actually grew, remove the old entry from the free
  // list and add the new entry.
  if (newSize != oldSize) {
    // Remove the original block from the free list
    removeFreeBlock(oldBlock);

    // Save the new size in the block info and in the boundary tag
    // and tag it to show the preceding block is used (otherwise, it
    // would have become part of this one!).
    newBlock->sizeAndTags = newSize | TAG_PRECEDING_USED;
    // The boundary tag of the preceding block is the word immediately
    // preceding block in memory where we left off advancing blockCursor.
    *(size_t*)UNSCALED_POINTER_SUB(blockCursor, WORD_SIZE) = newSize | TAG_PRECEDING_USED;  

    // Put the new block in the free list.
    insertFreeBlock(newBlock);
  }
  return;
}

/* Get more heap space of size at least reqSize. */
static void requestMoreSpace(size_t reqSize) {
  size_t pagesize = mem_pagesize();
  size_t numPages = (reqSize + pagesize - 1) / pagesize;
  BlockInfo *newBlock;
  size_t totalSize = numPages * pagesize;
  size_t prevLastWordMask;

  void* mem_sbrk_result = mem_sbrk(totalSize);
  if ((size_t)mem_sbrk_result == -1) {
    printf("ERROR: mem_sbrk failed in requestMoreSpace\n");
    exit(0);
  }
  newBlock = (BlockInfo*)UNSCALED_POINTER_SUB(mem_sbrk_result, WORD_SIZE);

  /* initialize header, inherit TAG_PRECEDING_USED status from the
     previously useless last word however, reset the fake TAG_USED
     bit */
  prevLastWordMask = newBlock->sizeAndTags & TAG_PRECEDING_USED;
  newBlock->sizeAndTags = totalSize | prevLastWordMask;
  // Initialize boundary tag.
  ((BlockInfo*)UNSCALED_POINTER_ADD(newBlock, totalSize - WORD_SIZE))->sizeAndTags = 
    totalSize | prevLastWordMask;

  /* initialize "new" useless last word
     the previous block is free at this moment
     but this word is useless, so its use bit is set
     This trick lets us do the "normal" check even at the end of
     the heap and avoid a special check to see if the following
     block is the end of the heap... */
  *((size_t*)UNSCALED_POINTER_ADD(newBlock, totalSize)) = TAG_USED;

  // Add the new block to the free list and immediately coalesce newly
  // allocated memory space
  insertFreeBlock(newBlock);
  coalesceFreeBlock(newBlock);
}


/* Print the heap by iterating through it as an implicit free list. */
static void examine_heap() {
  BlockInfo *block;

  /* print to stderr so output isn't buffered and not output if we crash */
  fprintf(stderr, "FREE_LIST_HEAD: %p\n", (void *)FREE_LIST_HEAD);

  for (block = (BlockInfo *)UNSCALED_POINTER_ADD(mem_heap_lo(), WORD_SIZE); /* first block on hea\
									       p */
       SIZE(block->sizeAndTags) != 0 && (void*)block < (void*)mem_heap_hi();
       block = (BlockInfo *)UNSCALED_POINTER_ADD(block, SIZE(block->sizeAndTags))) {

    /* print out common block attributes */
    fprintf(stderr, "%p: %ld %ld %ld\t",
            (void *)block,
            SIZE(block->sizeAndTags),
            block->sizeAndTags & TAG_PRECEDING_USED,
            block->sizeAndTags & TAG_USED);

    /* and allocated/free specific data */
    if (block->sizeAndTags & TAG_USED) {
      fprintf(stderr, "ALLOCATED\n");
    } else {
      fprintf(stderr, "FREE\tnext: %p, prev: %p\n",
              (void *)block->next,
              (void *)block->prev);
    }
  }
  fprintf(stderr, "END OF HEAP\n\n");
}

/* Initialize the allocator. */
int mm_init () {
  // Head of the free list.
  BlockInfo *firstFreeBlock;

  // Initial heap size: WORD_SIZE byte heap-header (stores pointer to head
  // of free list), MIN_BLOCK_SIZE bytes of space, WORD_SIZE byte heap-footer.
  size_t initSize = WORD_SIZE+MIN_BLOCK_SIZE+WORD_SIZE;
  size_t totalSize;

  void* mem_sbrk_result = mem_sbrk(initSize);
  //  printf("mem_sbrk returned %p\n", mem_sbrk_result);
  if ((ssize_t)mem_sbrk_result == -1) {
    printf("ERROR: mem_sbrk failed in mm_init, returning %p\n", 
           mem_sbrk_result);
    exit(1);
  }

  firstFreeBlock = (BlockInfo*)UNSCALED_POINTER_ADD(mem_heap_lo(), WORD_SIZE);

  // Total usable size is full size minus heap-header and heap-footer words
  // NOTE: These are different than the "header" and "footer" of a block!
  // The heap-header is a pointer to the first free block in the free list.
  // The heap-footer is used to keep the data structures consistent (see
  // requestMoreSpace() for more info, but you should be able to ignore it).
  totalSize = initSize - WORD_SIZE - WORD_SIZE;

  // The heap starts with one free block, which we initialize now.
  firstFreeBlock->sizeAndTags = totalSize | TAG_PRECEDING_USED;
  firstFreeBlock->next = NULL;
  firstFreeBlock->prev = NULL;
  // boundary tag
  *((size_t*)UNSCALED_POINTER_ADD(firstFreeBlock, totalSize - WORD_SIZE)) = totalSize | TAG_PRECEDING_USED;
  
  // Tag "useless" word at end of heap as used.
  // This is the is the heap-footer.
  *((size_t*)UNSCALED_POINTER_SUB(mem_heap_hi(), WORD_SIZE - 1)) = TAG_USED;

  // set the head of the free list to this new free block.
  FREE_LIST_HEAD = firstFreeBlock;
  return 0;
}


// TOP-LEVEL ALLOCATOR INTERFACE ------------------------------------


/* Allocate a block of size size and return a pointer to it. */
void* mm_malloc (size_t size) {
	// Zero-size requests get NULL.
	if (size == 0)
		return NULL;

	size_t reqSize;
	BlockInfo* ptrFreeBlock = NULL;
	size_t blockSize;
	size_t precedingBlockUseTag;

	size += WORD_SIZE; // Add one word for the initial size header.

	// Make sure we allocate enough space for a blockInfo in case we free this block.
	if (size <= MIN_BLOCK_SIZE)
		reqSize = MIN_BLOCK_SIZE;
	else
		reqSize = ALIGNMENT * ((size + ALIGNMENT - 1) / ALIGNMENT); // Round up for correct alignment

	//Find enough free space
	ptrFreeBlock = (BlockInfo*) searchFreeList(reqSize);
	if(ptrFreeBlock == NULL) { // Get enough new heap space if there wasn't a big enough block free already
		requestMoreSpace(reqSize);
		ptrFreeBlock = (BlockInfo*) searchFreeList(reqSize);
	}
	removeFreeBlock(ptrFreeBlock); // Remove the found block from the free blocks linked list

	// Get info
	blockSize = SIZE(ptrFreeBlock->sizeAndTags); // Get the size of the found block
	size_t remainingFreeSize = blockSize - reqSize; // Get the amount of unneeded space in the found block
	precedingBlockUseTag = ptrFreeBlock->sizeAndTags & TAG_PRECEDING_USED; // Save the preceding_used bit
	size_t newTags = TAG_USED | precedingBlockUseTag; // Build a new tag for the allocated block

	if(remainingFreeSize >= MIN_BLOCK_SIZE) { // If there is enough space left for a smaller free block, make one
		ptrFreeBlock->sizeAndTags = reqSize; // Set the allocated block's size to
		BlockInfo* newFreeBlock = (BlockInfo*) UNSCALED_POINTER_ADD(ptrFreeBlock,reqSize); // Initialize the new free block
		newFreeBlock->sizeAndTags = remainingFreeSize; // Set the new free block's size
		newFreeBlock->sizeAndTags |= TAG_PRECEDING_USED; // Set the new free block's preceding_used bit to one
		newFreeBlock->sizeAndTags &= ~TAG_USED; // Set the new free block's used bit to zero
		*((size_t*) UNSCALED_POINTER_ADD(ptrFreeBlock,blockSize-WORD_SIZE)) = newFreeBlock->sizeAndTags; // Set the new free block's footer
		insertFreeBlock(newFreeBlock); // Add the new free block to the free blocks linked list
	} else { // Otherwise, just allocate the extra space as well
		BlockInfo* followingBlock = (BlockInfo*) UNSCALED_POINTER_ADD(ptrFreeBlock,blockSize); // Get the following block
		followingBlock->sizeAndTags |= TAG_PRECEDING_USED; // Set the following block's preceding_used bit to one
		if((followingBlock->sizeAndTags & TAG_USED) == 0) // If the following block is not used
			*((size_t*) UNSCALED_POINTER_ADD(followingBlock,SIZE(followingBlock->sizeAndTags)-WORD_SIZE)) = followingBlock->sizeAndTags; // Set the following block's footer
	}

	ptrFreeBlock->sizeAndTags |= newTags; // Add the new tags to the allocated block
	return (UNSCALED_POINTER_ADD(ptrFreeBlock,WORD_SIZE)); // Return pointer to data after sizeAndTags
}

/* Free the block referenced by ptr. */
void mm_free (void *ptr) {
	// Make sure ptr is within the heap and freeable
	if(ptr > mem_heap_hi() - MIN_BLOCK_SIZE)
		return;

	size_t payloadSize;
	BlockInfo* blockInfo;
	BlockInfo* followingBlock;

	// Get info
	blockInfo = (BlockInfo*) UNSCALED_POINTER_SUB(ptr,WORD_SIZE); // Get the block to free
	payloadSize = SIZE(blockInfo->sizeAndTags); // Get the size of the block to free
	followingBlock = (BlockInfo*) UNSCALED_POINTER_ADD(blockInfo,payloadSize); // Get the following block

	// Set tags
	blockInfo->sizeAndTags &= ~TAG_USED; // Set the block's used bit to zero
	*((size_t*) UNSCALED_POINTER_ADD(blockInfo,payloadSize-WORD_SIZE)) = blockInfo->sizeAndTags; // Set the block's footer
	followingBlock->sizeAndTags &= ~TAG_PRECEDING_USED; // Set the following block's used bit to zero
	if((followingBlock->sizeAndTags & TAG_USED) == 0) // If the following block is not used
		*((size_t*) UNSCALED_POINTER_ADD(followingBlock,SIZE(followingBlock->sizeAndTags)-WORD_SIZE)) = followingBlock->sizeAndTags; // Set the following block's footer

	// Update linked list
	insertFreeBlock(blockInfo); // Insert block
	coalesceFreeBlock(blockInfo); // Coalesce block

	return;
}


// Implement a heap consistency checker as needed.
int mm_check() {
  return 0;
}

// Extra credit.
void* mm_realloc(void* ptr, size_t size) {
    // PTR is null, call malloc(size)
    if (ptr == NULL) {
        return mm_malloc(size);
    }

    // PTR is not null and size is 0, call free(ptr)
    if (ptr != NULL && size == 0) {
        mm_free(ptr);
        return NULL;
    }

    // Size, BlockInfo and FollowingBlockInfo of ptr
    size_t oldPayloadSize;
    BlockInfo* oldBlockInfo;
    BlockInfo* oldFollowingBlock;
    oldBlockInfo = (BlockInfo*) UNSCALED_POINTER_SUB(ptr, WORD_SIZE); // Get block to realloc
    oldPayloadSize = SIZE(oldBlockInfo->sizeAndTags); // Get size of block to realloc
    oldFollowingBlock = (BlockInfo*) UNSCALED_POINTER_ADD(oldBlockInfo, oldPayloadSize); // Get following block

    // Check if new and old size is the same, if so,
    // just return our current pointer since nothing will change
    // TODO: Is this fine with what he wants from Optional Extra Credit?
    if(oldPayloadSize == size) {
        return ptr;
    }

    // If our new size is smaller than our old size
    // Free memory outside of new size bytes
    if (oldPayloadSize > size) {
        // TODO: Remove unused byte blocks
        size_t precedingBlockUseTag = oldBlockInfo->sizeAndTags & TAG_PRECEDING_USED; // Save used bit
        size += WORD_SIZE; // Add 1 word for initial size header
        size_t reqSize; // Allocate enough space for our smaller block
        if (size <= MIN_BLOCK_SIZE)
            reqSize = MIN_BLOCK_SIZE;
        else
            reqSize = ALIGNMENT * ((size + ALIGNMENT - 1) / ALIGNMENT);
        size_t remainingFreeSize = oldPayloadSize - reqSize;
        oldBlockInfo->sizeAndTags = reqSize; // Set the block's new size
        oldBlockInfo->sizeAndTags |= (TAG_USED | precedingBlockUseTag); // Build and set a new tag 
        *((size_t*) UNSCALED_POINTER_ADD(oldBlockInfo, reqSize-WORD_SIZE)) = oldBlockInfo->sizeAndTags; // Set the block's new footer

        BlockInfo* newFreeBlock = (BlockInfo*) UNSCALED_POINTER_ADD(oldBlockInfo, reqSize);
        newFreeBlock->sizeAndTags = remainingFreeSize; // Set size of free block
        newFreeBlock->sizeAndTags |= (TAG_USED | precedingBlockUseTag); // Set preceding bit to one
        newFreeBlock->sizeAndTags &= ~TAG_USED; // Set used bit to zero
        *((size_t*) UNSCALED_POINTER_ADD(current, remainingFreeSize-WORD_SIZE)) = current->sizeAndTags; // Set the block's new footer
        return (UNSCALED_POINTER_ADD(oldBlockInfo, WORD_SIZE)); // Return pointer to data after sizeAndTags
    }

    /* From here on out, oldPayloadSize < newPayloadSize */

    /* TODO: // remove todo when done, leave the rest of the comment wheb dibe
     * Check if there is enoguh room in the next blocks over
     * If there is, we set those blocks as occupied for our
     * new memory occupations
     * Else, we run mm_malloc, free our old memory, and return
     * the newPtr we got from mm_malloc
     */

    int m = 0;
    while (0) { // Check if our next block is occupied
        // Set block as occupied here

        m++; // Increment size counter

        if (0) { // Check if we are at our required size here
            m = 0;
            while(0) { // Iterate through new blocks and set as occupied
                // Set new blocks as occupied here

                m++; // Increment size counter
            }

            return ptr; // Return old ptr
        }
    }

    // malloc new chunk of bytes and check if it succeeded
    void* newPtr = mm_malloc(size);
    if (newPtr == NULL) {
        return NULL;
    }

    free(ptr); // Free old memory

    return newPtr; // Return new location
}
