/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "team eight",
    /* First member's full name */
    "Jeein Choi",
    /* First member's email address */
    "chris309804@naver.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

#define ALIGNMENT 8                                         /* single word (4) or double word (8) alignment */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)       /* rounds up to the nearest multiple of ALIGNMENT */
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))                 /* adjusted size of the block */

#define WSIZE 4                                             /* word size*/
#define DSIZE 8                                             /* double word size*/
#define CHUNKSIZE (1<<12)                                   /* default increasing heap size*/

#define MAX(x, y) ((x) > (y)? (x) : (y))                    /* get max of x and y*/

#define PACK(size, alloc) ((size) | (alloc))                /* create data for header and footer block */

#define GET(p)      (*(unsigned int *)(p))                  /* get data from the header/footer */
#define PUT(p, val) (*(unsigned int *)(p) = (val))          /* set data to the header/footer */

#define GET_SIZE(p)     (GET(p) & ~0x7)                     /* get size of the block from the header/footer */
#define GET_ALLOC(p)    (GET(p) & 0x1)                      /* get allocated status from the header/footer */

#define HDRP(bp)        ((char *)(bp) - WSIZE)                          /* get the address of the header from the block pointer */
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)     /* get the address of the footer from the block pointer*/

#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))   /* get block pointer of the next block */
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))   /* get block pointer of the previous block */

static char* heap_listp;

static void *coalesce(void *bp);                                            /* if there are free blocks around the freed block, coalesce with them */
static void *find_fit(size_t asize);                                        /* find the free block to allocate */
static void place(void *bp, size_t asize);                                  /* set data to header and footer block of the allocated block */
static void *extend_heap(size_t words);                                     /* if heap is full extend it */

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *) - 1)                   /* create heap space to initialize heap */
        return -1;

    PUT(heap_listp, 0);                                                     /* unused block for alignment */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));                            /* prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));                            /* prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));                                /* epilogue header */
    heap_listp += (2*WSIZE);                                                /* fixed start block pointer */

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)                               /* extend heap by CHUNKSIZE */
        return -1;

    return 0;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;               /* create heap space that satisfies memory alignment */
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));                                           /* free block header */
    PUT(FTRP(bp), PACK(size, 0));                                           /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));                                   /* update epilogue header */

    return coalesce(bp);                                                    /* if there are free blocks around the newly created heap space, coalesce with them */
}

/* first fit */
static void *find_fit(size_t asize)
{
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {     /* find the first fit free block */
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    return NULL; /* No fit */
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));                                      /* size of the found block */

    if ((csize - asize) >= (2*DSIZE)) {                                     /* spliting the block to avoid internal fragmentation */
        PUT(HDRP(bp), PACK(asize, 1));                                      /* set header block of the allocated block*/
        PUT(FTRP(bp), PACK(asize, 1));                                      /* set footer block of the allocated block */
        bp = NEXT_BLKP(bp);                                                 /* block pointer for splited free block */
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else {                                                                  /* default: no split */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        return bp;
    }

    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    return bp;
}
/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL) {
        return mm_malloc(size);
    }
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    
    copySize = GET_SIZE(HDRP(oldptr));
    //copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;


    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}