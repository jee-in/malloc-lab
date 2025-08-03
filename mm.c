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
#define ASIZE(size) ((size) <= DSIZE ? 2 * DSIZE : DSIZE + ALIGN(size))

#define WSIZE 4                                             /* word size */
#define DSIZE 8                                             /* double word size */
#define CHUNKSIZE (1<<12)                                   /* default increasing heap size */

#define MAX(x, y) ((x) > (y)? (x) : (y))                    /* get max between x and y */
#define MIN(x, y) ((x) < (y)? (x) : (y))                    /* get min between x and y */

#define PACK(size, alloc) ((size) | (alloc))                /* create data for header and footer block */

#define GET(p)      (*(unsigned int *)(p))                  /* get data from the header/footer */
#define PUT(p, val) (*(unsigned int *)(p) = (val))          /* set data to the header/footer */

#define GET_SIZE(p)     (GET(p) & ~0x7)                     /* get size of the block from the header/footer */
#define GET_ALLOC(p)    (GET(p) & 0x1)                      /* get allocated status from the header/footer */

#define HDRP(bp)   ((char *)(bp) - WSIZE)                                   /* get the address of the header from the block pointer */
#define FTRP(bp)   ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)              /* get the address of the footer from the block pointer*/

#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))   /* get block pointer of the next block */
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))   /* get block pointer of the previous block */

#define NEXT_FREE(bp)   (*(char **)(bp))
#define PREV_FREE(bp)   (*(char **)(bp + WSIZE))

#define LISTLIMIT 10

static char* heap_listp;                                                    /* pointer to the heap top  */
static void *free_lists[LISTLIMIT];

static void *find_fit(size_t asize);                                        /* find the free block to allocate */
static void place(void *bp, size_t asize);                                  /* set data to header and footer block of the allocated block */
static void *extend_heap(size_t words);                                     /* if heap is full extend it */
static void *coalesce_free(void *bp);                                       /* if there are free blocks around the freed block, coalesce with them */

static void insert_free_block(void *bp);
static void remove_free_block(void *bp);

static int get_list_index(size_t size);

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
    for (int i = 0; i < LISTLIMIT; i++) {
        free_lists[i] = NULL;
    }

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)                               /* extend heap by CHUNKSIZE */
        return -1;

    return 0;
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

    /* Search the free block whose size satisfies the adjusted block size */
    asize = ASIZE(size);
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* Extend heap area if no free block available */
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
    coalesce_free(bp);
}

/*
 * mm_realloc - implement in-place realloc
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

    size_t oldsize = GET_SIZE(HDRP(oldptr));
    size_t copysize = oldsize - DSIZE;
    size_t asize = ASIZE(size);

    if (size < copysize)
      copysize = size;

    void *prevPtr = PREV_BLKP(oldptr);
    void *nextPtr = NEXT_BLKP(oldptr);

    size_t prev_alloc = GET_ALLOC(HDRP(prevPtr));
    size_t next_alloc = GET_ALLOC(HDRP(nextPtr));
    size_t prevSize = GET_SIZE(HDRP(prevPtr));
    size_t nextSize = GET_SIZE(HDRP(nextPtr));

    if (!prev_alloc && !next_alloc) {
        size_t totalSize = oldsize + prevSize + nextSize;

        if (totalSize >= asize && (totalSize - asize) >= 2 * DSIZE) {
            remove_free_block(prevPtr);
            remove_free_block(nextPtr);

            newptr = prevPtr;
            memmove(newptr, oldptr, copysize);
            PUT(HDRP(newptr), PACK(asize, 1));
            PUT(FTRP(newptr), PACK(asize, 1));

            void *freedp = NEXT_BLKP(newptr);
            PUT(HDRP(freedp), PACK(totalSize - asize, 0));
            PUT(FTRP(freedp), PACK(totalSize - asize, 0));
            
            insert_free_block(freedp);
            return newptr;
        }
    } else if (!prev_alloc && next_alloc) {
        size_t totalSize = oldsize + prevSize;

        if (totalSize >= asize && (totalSize - asize) >= 2 * DSIZE) {
            remove_free_block(prevPtr);
            newptr = prevPtr;
            memmove(newptr, oldptr, copysize);
            PUT(HDRP(newptr), PACK(asize, 1));
            PUT(FTRP(newptr), PACK(asize, 1));

            void *freedp = NEXT_BLKP(newptr);
            PUT(HDRP(freedp), PACK(totalSize - asize, 0));
            PUT(FTRP(freedp), PACK(totalSize - asize, 0));

            insert_free_block(freedp);
            return newptr;
        }
    } else if (prev_alloc && !next_alloc) {
        size_t totalSize = oldsize + nextSize;

        if (totalSize >= asize && (totalSize - asize) >= 2 * DSIZE) {
            remove_free_block(nextPtr);
            newptr = oldptr;
            PUT(HDRP(newptr), PACK(asize, 1));
            PUT(FTRP(newptr), PACK(asize, 1));

            void *freedp = NEXT_BLKP(newptr);
            PUT(HDRP(freedp), PACK(totalSize - asize, 0));
            PUT(FTRP(freedp), PACK(totalSize - asize, 0));

            insert_free_block(freedp);
            return newptr;
        }        
    } else {
        if (oldsize >= asize && (oldsize - asize) >= 2 * DSIZE) {
            newptr = oldptr;
            PUT(HDRP(newptr), PACK(asize, 1));
            PUT(FTRP(newptr), PACK(asize, 1));
            
            void *freedp = NEXT_BLKP(newptr);
            PUT(HDRP(freedp), PACK(oldsize - asize, 0));
            PUT(FTRP(freedp), PACK(oldsize - asize, 0));

            insert_free_block(freedp);
            return newptr;
        }
    }

    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;

    memcpy(newptr, oldptr, copysize);
    mm_free(oldptr);
    return newptr;
}

/* first-fit */
static void *find_fit(size_t asize)
{
    int idx;
    void *bp;

    for (idx = get_list_index(asize); idx < LISTLIMIT; idx++) {
        for (bp = free_lists[idx]; bp != NULL; bp = NEXT_FREE(bp)) {
            if (!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp))) {
                return bp;
            }
        }
    }

    return NULL;
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));                                      /* size of the found block */
    remove_free_block(bp);

    if ((csize - asize) >= (2*DSIZE)) {                                     /* spliting the block to avoid internal fragmentation */
        PUT(HDRP(bp), PACK(asize, 1));                                      /* set header block of the allocated block*/
        PUT(FTRP(bp), PACK(asize, 1));                                      /* set footer block of the allocated block */
        
        bp = NEXT_BLKP(bp);                                                 /* block pointer for splited free block */
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));

        coalesce_free(bp);
    }
    else {                                                                  /* default: no split */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
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
    NEXT_FREE(bp) = NULL;
    PREV_FREE(bp) = NULL;    

    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));                                   /* update epilogue header */
    
    return coalesce_free(bp);
}

static void *coalesce_free(void *bp) {
    void *prev_bp = PREV_BLKP(bp);
    void *next_bp = NEXT_BLKP(bp);
    size_t prev_alloc = GET_ALLOC(FTRP(prev_bp));
    size_t next_alloc = GET_ALLOC(HDRP(next_bp));
    size_t size = GET_SIZE(HDRP(bp));

    if (!prev_alloc) {
        remove_free_block(prev_bp);
        size += GET_SIZE(HDRP(prev_bp));
        bp = prev_bp;
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    if (!next_alloc) {
        remove_free_block(next_bp);
        size += GET_SIZE(HDRP(next_bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    insert_free_block(bp);
    return bp;
}

static void insert_free_block(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));
    int index = get_list_index(size);

    void *head = free_lists[index];

    if (head != NULL) {
        PREV_FREE(head) = bp;
    }
    NEXT_FREE(bp) = head;
    PREV_FREE(bp) = NULL;

    free_lists[index] = bp;
}

static void remove_free_block(void *bp) {
    int index = get_list_index(GET_SIZE(HDRP(bp)));
    void *prev = PREV_FREE(bp);
    void *next = NEXT_FREE(bp);

    if (prev != NULL) {
        NEXT_FREE(prev) = next;
    } else {
        free_lists[index] = next;
    }

    if (next != NULL) {
        PREV_FREE(next) = prev;
    }
}


static int get_list_index(size_t size) {
    if (size <= (1 << 4)) return 0;
    else if (size <= (1 << 5)) return 1;
    else if (size <= (1 << 6)) return 2;
    else if (size <= (1 << 7)) return 3;
    else if (size <= (1 << 8)) return 4;
    else if (size <= (1 << 9)) return 5;
    else if (size <= (1 << 10)) return 6;
    else if (size <= (1 << 11)) return 7;
    else if (size <= (1 << 12)) return 8;
    else return LISTLIMIT - 1;
}