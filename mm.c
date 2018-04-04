/*********************************************************************************
 *      Copyright:  (C) 2018 XiaoAn Science and Technology Co.,Ltd.
 *                  All rights reserved.
 *
 *      Filename:  my_mm.c
 *     Description:  the free block is restored into seg lists, such as
 *     list[0] is the address of the free block list header,each list has free blocks
 *     of size class 2^n to 2^(n+1)-1
 *
 *     
 *        Version:  1.0.0(2018年03月29日)
 *         Author:  zhangjinhao <zhangqi336@outlook.com>
 *      ChangeLog:  1, Release initial version on "2018年03月29日 10时00分49秒"
 *                 
 ********************************************************************************/
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

#define WSIZE      4 /*  Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /*  Doubleword size (bytes) */
#define CHUNKSIZE  (1 << 6)      /*  Extend heap by this amount (bytes) */ 

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc)  ((size) | (alloc))

#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

#define GET_SIZE(p)   (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p)  (GET(p) & 0x1)

#define HDRP(bp)  ((void *)(bp) - WSIZE)
#define FTRP(bp)  ((void *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 

#define GET_PREV(bp)       ((char *)bp)
#define GET_NEXT(bp)       ((char *)(bp) + WSIZE)
#define GET_PREV_BLK(bp)   (*(char **)(bp))
#define GET_NEXT_BLK(bp)   (*(char **)(GET_NEXT(bp)))

#define PUT_PTR(p, ptr)    (*(unsigned int *)(p) = (unsigned int)(ptr))

#define SET_NEXT_PTR(bp, qp) (GET_NEXT_PTR(bp) = qp)
#define SET_PREV_PTR(bp, qp) (GET_PREV_PTR(bp) = qp)

#define SEG_LIST_COUNT  20 
#define SEG_LIST(ptr, index)  *((char **)ptr+index)

#define ALIGN(size) (((size) + (8-1)) & ~0x7)

static char *heap_listp = 0; 
static void *seg_listp;

static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void *place(void *bp, size_t asize);


static void insert_free_block(void *bp, size_t block_size); 
static void remove_free_block(void *bp); 



team_t team = {
    /*  Team name */
    "haojinzhangs",
    /*  First member's full name */
    "haojinzhang",
    /*  First member's email address */ 
    "zhangqi336@outlook.com",
    /*  Second member's full name (leave blank if none) */
    "haojinzhang",
    /*  Second member's email address (leave blank if none) */
    "zhangqi336@outlook.com"
};

/* empty   block :head<4>
 *                prev_bp<4>
 *                next_bp<4>
 *                foot<4>*/

/* alloced block : head<4>
 *                 payload[]
 *                 foot<4>*/

/* initialize the memory manager. */
int  mm_init(void)
{
    int list_number;
    

    seg_listp = mem_sbrk(SEG_LIST_COUNT*WSIZE);


    for (list_number = 0; list_number < SEG_LIST_COUNT; list_number++) 
    {
        SEG_LIST(seg_listp, list_number)= NULL;
    }

    if ((heap_listp = mem_sbrk(4*WSIZE)) == NULL) 
        return -1;
   
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); 
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));  
    heap_listp += 2*WSIZE; 


    if (!extend_heap(CHUNKSIZE/WSIZE))
        return -1;
    return 0;
}

static void *coalesce(void *bp)
{
   size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
   size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
   size_t size = GET_SIZE(HDRP(bp));


   if(prev_alloc && next_alloc)
       return bp;
   else if(prev_alloc && !next_alloc)
   {
       remove_free_block(bp);
       remove_free_block(NEXT_BLKP(bp));
       size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
       PUT(HDRP(bp), PACK(size, 0));
       PUT(FTRP(bp), PACK(size, 0));
   }
   else if (!prev_alloc && next_alloc) 
   {
        remove_free_block(bp);
        remove_free_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
   }
   else if(!prev_alloc && !next_alloc)
   {
       remove_free_block(PREV_BLKP(bp));
       remove_free_block(bp);
       remove_free_block(NEXT_BLKP(bp));
       size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
       PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
       PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
       bp = PREV_BLKP(bp); 
   }
   insert_free_block(bp, size);
   return bp;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words%2) ? (words+1)*WSIZE : words*WSIZE;
    if(size<16)
        size = 16;

    if ((int)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0)); 
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    insert_free_block(bp, size);

    return coalesce(bp);
}


static void *find_fit(size_t asize)
{
    size_t size = asize;
    int list_number = 0;
    void *list_ptr = NULL;

    while (list_number < SEG_LIST_COUNT) 
    {
        if ((list_number == SEG_LIST_COUNT - 1) || ((size <= 1) && (SEG_LIST(seg_listp, list_number)!= NULL)))
        {
            list_ptr  = SEG_LIST(seg_listp, list_number);
            while ((list_ptr != NULL) && (asize > GET_SIZE(HDRP(list_ptr))))
            {
                list_ptr = GET_PREV_BLK(list_ptr);

            }
            if(list_ptr != NULL)
                break;
        }
        list_number++;
        size =size>>1;
    
    }

    return list_ptr;
}


static void insert_free_block(void *bp, size_t block_size)
{
    void  *list_ptr = NULL;
    void *insert_loc = NULL;

    int list_number = 0; 

    while ((list_number < (SEG_LIST_COUNT - 1)) && (block_size > 1))
    {
         block_size = block_size >> 1;
         list_number++;
    }

    list_ptr = SEG_LIST(seg_listp, list_number);

    while ((list_ptr != NULL) && (block_size > GET_SIZE(HDRP(list_ptr))))
    {
        insert_loc = list_ptr;
        list_ptr = GET_PREV_BLK(list_ptr);
    }

    if (list_ptr) 
    {
        if (insert_loc)
        {
            PUT_PTR(GET_PREV(insert_loc), bp);
            PUT_PTR(GET_NEXT(bp), insert_loc);
            PUT_PTR(GET_PREV(bp), list_ptr);
            PUT_PTR(GET_NEXT(list_ptr), bp); 
        }
        else // bp smaller than first item in list_ptr, insert at start
        {
            PUT_PTR(GET_NEXT(list_ptr), bp);
            PUT_PTR(GET_PREV(bp), list_ptr);
            PUT_PTR(GET_NEXT(bp), NULL);
            SEG_LIST(seg_listp, list_number)=bp;
        }
    }
    else
    {
        if (insert_loc) 
        {
            PUT_PTR(GET_NEXT(bp), insert_loc);
            PUT_PTR(GET_PREV(insert_loc), bp);
            PUT_PTR(GET_PREV(bp), NULL);    
        }
        else 
        {
            SEG_LIST(seg_listp, list_number)= bp;
            PUT_PTR(GET_PREV(bp), NULL);
            PUT_PTR(GET_NEXT(bp), NULL);
            return;
        }
    }
    return;
}


static void remove_free_block(void *bp)
{
    int list_number = 0;
    size_t  block_size = GET_SIZE(HDRP(bp));

    if(!GET_NEXT_BLK(bp))
    {
        while((list_number<(SEG_LIST_COUNT-1))&& block_size>1)
        {
            list_number++;
            block_size = block_size>>1;
        }
        SEG_LIST(seg_listp, list_number)= GET_PREV_BLK(bp);
        if(SEG_LIST(seg_listp, list_number) != NULL) 
            PUT_PTR(GET_NEXT(SEG_LIST(seg_listp, list_number)), NULL);
        return;
    }
    else
    {
        PUT_PTR(GET_PREV(GET_NEXT_BLK(bp)), GET_PREV_BLK(bp));
        if (GET_PREV_BLK(bp) != NULL)
            PUT_PTR(GET_NEXT(GET_PREV_BLK(bp)), GET_NEXT_BLK(bp));
    }
    return;
}


static void *place(void *bp, size_t asize)
{
    void *np = NULL;
    size_t csize = GET_SIZE(HDRP(bp));
    remove_free_block(bp);

    if ((csize - asize) >= (2*DSIZE)) 
    {
        if ((csize - asize) >= 200)
        {
            PUT(HDRP(bp), PACK(csize-asize, 0));
            PUT(FTRP(bp), PACK(csize-asize, 0));
            np = NEXT_BLKP(bp);
            PUT(HDRP(np), PACK(asize, 1));  
            PUT(FTRP(np), PACK(asize, 1)); 
            insert_free_block(bp, csize - asize);
            return np;
        }
        else
        {
            PUT(HDRP(bp), PACK(asize, 1)); 
            PUT(FTRP(bp), PACK(asize, 1));
            np = NEXT_BLKP(bp);
            PUT(HDRP(np), PACK(csize - asize, 0));
            PUT(FTRP(np), PACK(csize - asize, 0));
            insert_free_block(np, csize - asize); 
        }
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
    return bp;
}


void *mm_malloc(size_t size)
{
    size_t asize;  /* adjusted block size */ 
    size_t extendsize; 
    char *bp;
    char *ptr;

    if(size==0)
        return NULL;

    if(size<DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE*((size + (DSIZE)+(DSIZE - 1))/DSIZE);

    if((bp=find_fit(asize)) != NULL)
    {
        ptr = place(bp,asize);
        return ptr;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    ptr =  place(bp, asize);
    return ptr;

}

void mm_free(void *bp)//for allocate block
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    
    insert_free_block(bp, size);
    coalesce(bp);
}

void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    void *nextptr;
    size_t copysize,asize,csize;

    if(!size)
    {
        mm_free(oldptr);
        return NULL;
    }

    if(!oldptr)
    {
        return mm_malloc(size);
    }
    asize = ALIGN(size);//round up to (n*8) bytes

    copysize = GET_SIZE(HDRP(oldptr))-DSIZE;
    if(copysize == asize)
        return oldptr;

    /* if oldsize > size,the old ptr can hold the new size */
    if(asize < copysize)
    {
        if(copysize-asize-DSIZE <= DSIZE)
            return oldptr;

        PUT(HDRP(oldptr), PACK(asize + DSIZE, 1));
        PUT(FTRP(oldptr), PACK(asize + DSIZE, 1));
        newptr = oldptr;
        oldptr = NEXT_BLKP(newptr);
        PUT(HDRP(oldptr), PACK(copysize - asize, 0));
        PUT(FTRP(oldptr), PACK(copysize - asize, 0));
        insert_free_block(oldptr, GET_SIZE(HDRP(oldptr)));
        coalesce(oldptr);
        return newptr;
    }

    /* if size > oldsize    integrate the near free block until satisfy size*/
    nextptr = NEXT_BLKP(oldptr);
    if (nextptr != NULL && !GET_ALLOC(HDRP(nextptr))) 
    {
        csize = GET_SIZE(HDRP(nextptr));
        if (csize + copysize >= asize)
        {
            remove_free_block(nextptr);
            if(csize + copysize - asize <= DSIZE)//if remaining space less than DSIZE, use it all
            {
                PUT(HDRP(oldptr), PACK(copysize + DSIZE + csize, 1));
                PUT(FTRP(oldptr), PACK(copysize + DSIZE + csize, 1));
                return oldptr;
            }
            else
            {
                PUT(HDRP(oldptr), PACK(asize + DSIZE, 1));
                PUT(FTRP(oldptr), PACK(asize + DSIZE, 1));
                newptr = oldptr;
                oldptr = NEXT_BLKP(newptr);
                PUT(HDRP(oldptr), PACK(copysize + csize - asize, 0));
                PUT(FTRP(oldptr), PACK(copysize + csize - asize, 0));
                insert_free_block(oldptr, GET_SIZE(HDRP(oldptr)));
                coalesce(oldptr);
                return newptr;
            }
        }
    }

    /* lastly we have to allocate a free to fit new size  */
    newptr = mm_malloc(size); 
    if(!newptr)
        return NULL;

    memcpy(newptr, oldptr, copysize);
    mm_free(oldptr);
    return newptr;
}







