/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  Blocks are never coalesced or reused.  The size of
 * a block is found at the first aligned word before the block (we need
 * it for realloc).
 *
 * This code is correct and blazingly fast, but very bad usage-wise since
 * it never frees anything.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif




#define NEXT_FITx

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       (4)       /* Word and header/footer size (bytes) */ //line:vm:mm:beginconst
#define DSIZE       (8)       /* Double word size (bytes) */
// #define CHUNKSIZE  (400)  /* Extend heap by this amount (bytes) */  //line:vm:mm:endconst 
#define MIN_BLK_SIZE (24) /* Minimum block size */

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) //line:vm:mm:pack

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            //line:vm:mm:get
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    //line:vm:mm:put
#define GET_PTR(p) ((p) ? (void *)*(size_t *)(p) : 0)
#define PUT_PTR(p, ptr) ((p) ? *(size_t *)(p) = (size_t)(ptr) : 0)

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   //line:vm:mm:getsize
#define GET_ALLOC(p) (GET(p) & 0x1)                    //line:vm:mm:getalloc
#define GET_L_ALLOC(p) (GET(p) & 0x2)               //line:vm:mm:getprevalloc
/* Given block ptr bp, compute address of its header and footer */
#define HEADER(bp)       ((char *)(bp) - WSIZE)                      //line:vm:mm:hdrp
#define PREV_BLK(bp) ((char *)(bp))
#define NEXT_BLK(bp) ((bp) ? (char *)(bp) + DSIZE : (char *)0)
#define PREV_BLK_PTR(bp) (GET_PTR(PREV_BLK(bp)))
#define NEXT_BLK_PTR(bp) (GET_PTR(NEXT_BLK(bp)))
#define FOOTER(bp)       ((char *)(bp) + GET_SIZE(HEADER(bp)) - DSIZE) //line:vm:mm:ftrp

/* Given block ptr bp, compute address of next and previous blocks */
#define R_BLK(bp)  ((char *)(bp) + GET_SIZE(((HEADER(bp))))) //line:vm:mm:nextblkp
#define L_BLK(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) //line:vm:mm:prevblkp
/* $end mallocmacros */

/* Global variables */
static char *heap_listp=0;  /* Pointer to first block */  
#ifdef NEXT_FIT
static char *rover;           /* Next fit rover */
#endif


/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


/**
 * free list operations
 */
static inline void list_delete(void *bp) {
  PUT_PTR(NEXT_BLK(PREV_BLK_PTR(bp)), NEXT_BLK_PTR(bp));
  PUT_PTR(PREV_BLK(NEXT_BLK_PTR(bp)), PREV_BLK_PTR(bp));
}
static inline void list_insert(void *bp) {
  void *last_blk = NEXT_BLK_PTR(heap_listp);
  PUT_PTR(PREV_BLK(last_blk), bp);
  PUT_PTR(NEXT_BLK(bp), last_blk);
  PUT_PTR(PREV_BLK(bp), heap_listp);
  PUT_PTR(NEXT_BLK(heap_listp), bp);
}
static inline void set_alloc(void *bp, size_t size, unsigned alloc) {
  PUT(HEADER(bp), PACK(size, GET_L_ALLOC(HEADER(bp)) | alloc));
  if (!alloc) PUT(FOOTER(bp), PACK(size, GET_L_ALLOC(HEADER(bp)) | alloc));
  PUT(HEADER(R_BLK(bp)), PACK(GET_SIZE(HEADER(R_BLK(bp))), alloc << 1 | GET_ALLOC(HEADER(R_BLK(bp)))));
}

static void *coalesce(void *bp) {
  // dbg_printf("coalesce_and_add, bp = %p\n", bp);
  size_t size = GET_SIZE(HEADER(bp));
  if (!GET_L_ALLOC(HEADER(bp))) {
    // dbg_printf("coalesce left, bp = %p\n", L_BLK(bp));
    size += GET_SIZE(FOOTER(L_BLK(bp)));
    list_delete(L_BLK(bp));
    bp = L_BLK(bp);
    set_alloc(bp, size, 0);
  }
  if (!GET_ALLOC(HEADER(R_BLK(bp)))) {
    // dbg_printf("coalesce right, bp = %p\n", R_BLK(bp));
    size += GET_SIZE(HEADER(R_BLK(bp)));
    list_delete(R_BLK(bp));
    set_alloc(bp, size, 0);
  }
  // dbg_printf("coalesce size = %ld, bp = %p\n", size, bp);
  list_insert(bp);
  return bp;
}

/*
 * place - Place block of size bytes at start of block bp (MAYBE NOT FREE)
 *     and split if remainder would be at least minimum block size.
 */
static void place(void *bp, size_t size) {
  size_t blk_size = GET_SIZE(HEADER(bp));
  unsigned is_alloc = GET_ALLOC(HEADER(bp));
  if (blk_size >= size + MIN_BLK_SIZE) { 
    //split
    set_alloc(bp, size, 1);
    set_alloc(R_BLK(bp), blk_size - size, 0);
    if (is_alloc) list_insert(R_BLK(bp));
    else {
      PUT_PTR(NEXT_BLK(PREV_BLK_PTR(bp)), R_BLK(bp));
      PUT_PTR(PREV_BLK(NEXT_BLK_PTR(bp)), R_BLK(bp));
      PUT_PTR(PREV_BLK(R_BLK(bp)), PREV_BLK_PTR(bp));
      PUT_PTR(NEXT_BLK(R_BLK(bp)), NEXT_BLK_PTR(bp));
    }
    // dbg_printf("place: %p %ld\n", bp, blk_size);
  } else {
    if (!is_alloc) list_delete(bp);
    set_alloc(bp, blk_size, 1);
  }
}
/*
 * extend_heap - Extend heap by calling mem_sbrk and return the new block bp.
 *      Also add the new block to the free list and coalesce if necessary.
 */
static void *extend_heap(size_t size) {
  void *bp = mem_sbrk(size);
  if (bp == (void *)-1) return NULL;
  set_alloc(bp, size, 0);
  /* new epilogue header */
  PUT(HEADER(R_BLK(bp)), PACK(0, GET_L_ALLOC(HEADER(R_BLK(bp))) | 1));
  return coalesce(bp);
}

/* 
 * mm_init - initialize the malloc package!
 */
int mm_init(void)
{
     /* Create the initial empty heap */
    heap_listp = mem_sbrk(8*WSIZE);
    // dbg_printf("heap_start = %ud\n", (unsigned)heap_listp);
    if (heap_listp == (void *)-1) //line:vm:mm:begininit
        return -1;                         /* alignment padding */
    PUT(heap_listp, 0);                          
    PUT(heap_listp + 1 * WSIZE, PACK(6 * WSIZE, 3)); /* prologue header */
    PUT_PTR(heap_listp + 2 * WSIZE, 0);              /* prev pointer */
    PUT_PTR(heap_listp + 4 * WSIZE, 0);              /* next pointer */
    PUT(heap_listp + 6 * WSIZE, PACK(6 * WSIZE, 3)); /* prologue footer */
    PUT(heap_listp + 7 * WSIZE, PACK(0, 3));         /* epilogue header */
    heap_listp += 2 * WSIZE;
    
    // dbg_printf("heap_size = %ld\n", mem_heapsize());
    
    return 0;
}

/*
 * malloc - Allocate a block by incrementing the brk pointer.
 *      Always allocate a block whose size is a multiple of the alignment.
 */
void *malloc(size_t size)
{
  size = ALIGN(MAX(MIN_BLK_SIZE, size + WSIZE));
  for (void *bp = NEXT_BLK_PTR(heap_listp); bp!=NULL ; bp = NEXT_BLK_PTR(bp)) /* explicit free list */
    if (GET_SIZE(HEADER(bp)) >= size) {
      // dbg_printf("found! %u\n", GET_SIZE(HEADER(bp)));
      place(bp, size);
      // dbg_printf("place done, bp = %p\n", bp);
      return bp;
    }
  // dbg_printf("extend_heap %ld\n", MAX(CHUNKSIZE, size));
  /* need to extend the heap */
  void* bp = extend_heap(size);
  // dbg_printf("extend_heap done, bp = %p\n", bp);
  if (bp != NULL) place(bp, size);
  return bp;
}

/*
 * free - We don't know how to free a block.  So we ignore this call.
 *      Computers have big memories; surely it won't be a problem.
 */
void free(void *ptr){
  // dbg_printf("free %p\n", ptr);
	if (ptr < mem_heap_lo() || ptr > mem_heap_hi()) return;
  size_t size = GET_SIZE(HEADER(ptr));
  set_alloc(ptr, size, 0);
  coalesce(ptr);

}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.  I'm too lazy
 *      to do better.
 */
void *realloc(void *oldptr, size_t size)
{
  size_t oldsize;
  void *newptr;
  // dbg_printf("realloc %p %ld\n", oldptr, size);

  /* If size == 0 then this is just free, and we return NULL. */
  if(size == 0) {
    free(oldptr);
    return 0;
  }

  /* If oldptr is NULL, then this is just malloc. */
  if(oldptr == NULL) {
    return malloc(size);
  }

  /* Copy the old data. */
  oldsize = GET_SIZE(HEADER(oldptr));
  size = ALIGN(MAX(MIN_BLK_SIZE, size + WSIZE));

  if(size <= oldsize){
    place(oldptr, size);
    newptr=oldptr;
  } 
  else if (!GET_ALLOC(HEADER(R_BLK(oldptr))) && GET_SIZE(HEADER(R_BLK(oldptr))) + oldsize >= size){
  // allocate the right unallocated block
    list_delete(R_BLK(oldptr));
    size_t merge_size = GET_SIZE(HEADER(R_BLK(oldptr))) + oldsize;
    set_alloc(oldptr, merge_size, 1);
    place(oldptr, size);
    newptr=oldptr;
  }
  else{
    newptr = malloc(size);
    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
      return 0;
    }
    memcpy(newptr, oldptr, oldsize);
    /* Free the old block. */
    free(oldptr);
  }


  return newptr;
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc (size_t nmemb, size_t size)
{
  // dbg_printf("calloc %ld %ld\n", nmemb, size);
  size_t bytes = nmemb * size;
  void *newptr = malloc(bytes);
  memset(newptr, 0, bytes);

  return newptr;
}

/*
 * mm_checkheap - There are no bugs in my code, so I don't need to check,
 *      so nah!
 */
void mm_checkheap(int verbose){
	/*Get gcc to be quiet. */
	verbose = verbose;
  return;
}