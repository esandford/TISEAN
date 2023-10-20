/*
 *   This file is part of TISEAN
 *
 *   Copyright (c) 1998-2007 Rainer Hegger, Holger Kantz, Thomas Schreiber
 *
 *   TISEAN is free software; you can redistribute it and/or modify
 *   it under the terms of the GNU General Public License as published by
 *   the Free Software Foundation; either version 2 of the License, or
 *   (at your option) any later version.
 *
 *   TISEAN is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   GNU General Public License for more details.
 *
 *   You should have received a copy of the GNU General Public License
 *   along with TISEAN; if not, write to the Free Software
 *   Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
 */
/*Author: Rainer Hegger. Last modified May 10, 2000 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <limits.h>
#include <time.h>
#include "routines/tsa.h"

#define WID_STR "Estimates the correlation sum, -dimension and -entropy"

/* output is written every WHEN seconds */
#define WHEN 120
/* Size of the field for box assisted neighbour searching 
   (has to be a power of 2)*/
#define NMAX 256
/* Size of the box for the scramble routine */
#define SCBOX 4096

double **series;
long *scr;
char dimset=0,rescale_set=0,eps_min_set=0,eps_max_set=0;
char *FOUT=NULL;
double epsfactor,epsinv,lneps,lnfac;
double EPSMAX=1.0,EPSMIN=1.e-3;
double min,interval;
int imax=NMAX-1,howoften1,imin;
long box[NMAX][NMAX],*list,boxc1[NMAX],*listc1;
unsigned long nmax;
double **found,*norm;
unsigned long MINDIST=0,MAXFOUND=1000;
unsigned long length=ULONG_MAX,exclude=0;
unsigned int DIM=1,EMBED=10,HOWOFTEN=100,DELAY=1;
unsigned int verbosity=0x1;
char *column=NULL;
char *infile=NULL;

//explain what this program does
void show_options(char *progname)
{
  what_i_do(progname,WID_STR);
  fprintf(stderr,"  Usage: %s [options]\n",progname);
  fprintf(stderr,"  Options:\n");
  fprintf(stderr,"Everything not being a valid option will be interpreted as a possible"
          " datafile.\nIf no datafile is given stdin is read. Just - also"
          " means stdin\n");
  fprintf(stderr,"\t-l datapoints [default is whole file]\n");
  fprintf(stderr,"\t-x exclude # points [default 0]\n");
  fprintf(stderr,"\t-d delay  [default 1]\n");
  fprintf(stderr,"\t-M # of components, max. embedding dim. [default 1,10]\n");
  fprintf(stderr,"\t-c columns [default 1,...,# of components]\n");
  fprintf(stderr,"\t-t theiler-window [default 0]\n");
  fprintf(stderr,"\t-R max-epsilon [default: max data interval]\n");
  fprintf(stderr,"\t-r min-epsilon [default: (max data interval)/1000]\n");
  fprintf(stderr,"\t-# #-of-epsilons [default 100]\n");
  fprintf(stderr,"\t-N max-#-of-pairs (0 means all) [default 1000]\n");
  fprintf(stderr,"\t-E use rescaled data [default: not rescaled]\n");
  fprintf(stderr," \t-o outfiles [without exts.! default datafile[.d2][.h2][.stat][.c2]]\n");
  fprintf(stderr,"\t-V verbosity level [default: 1]\n\t\t"
          "0='only panic messages'\n\t\t"
          "1='+ input/output messages'\n\t\t"
          "2='+ output message each time output is done\n");
  fprintf(stderr,"\t-h show these options\n");
  fprintf(stderr,"\n");
  exit(0);
}

// read in arguments
void scan_options(int n,char **argv)
{
  char *out;
  //see ./routines/check_option.c
  if ((out=check_option(argv,n,'l','u')) != NULL)
    sscanf(out,"%lu",&length);
  if ((out=check_option(argv,n,'x','u')) != NULL)
    sscanf(out,"%lu",&exclude);
  if ((out=check_option(argv,n,'c','s')) != NULL)
    column=out;
  if ((out=check_option(argv,n,'d','u')) != NULL)
    sscanf(out,"%u",&DELAY);
  if ((out=check_option(argv,n,'M','2')) != NULL) {
    sscanf(out,"%u,%u",&DIM,&EMBED);
    dimset=1;
  }
  if ((out=check_option(argv,n,'t','u')) != NULL)
    sscanf(out,"%lu",&MINDIST);
  if ((out=check_option(argv,n,'R','f')) != NULL) {
    sscanf(out,"%lf",&EPSMAX);
    eps_max_set=1;
  }
  if ((out=check_option(argv,n,'r','f')) != NULL) {
    sscanf(out,"%lf",&EPSMIN);
    eps_min_set=1;
  }
  if ((out=check_option(argv,n,'#','u')) != NULL)
    sscanf(out,"%u",&HOWOFTEN);
  if ((out=check_option(argv,n,'N','u')) != NULL) {
    sscanf(out,"%lu",&MAXFOUND);
    if (MAXFOUND == 0)
      MAXFOUND=ULONG_MAX;
  }
  if ((out=check_option(argv,n,'E','n')) != NULL)
    rescale_set=1;
  if ((out=check_option(argv,n,'V','u')) != NULL)
    sscanf(out,"%u",&verbosity);
  if ((out=check_option(argv,n,'o','o')) != NULL)
    if (strlen(out) > 0)
      FOUT=out;
}

// deterministic scrambling of indices
void scramble(void)
{
  long i,j,k,m;
  unsigned long rnd,rndf,hlength,allscr=0;
  long *scfound,*scnhelp,scnfound;
  long scbox[SCBOX],lswap,element,scbox1=SCBOX-1;
  double *rz,*schelp,sceps=(double)SCBOX-0.001,swap;
  
  //length of time series - ((max embedding dimension-1)*delay)
  // = length of time series - length of delay vector
  hlength=length-(EMBED-1)*DELAY;

  if (sizeof(long) == 8) {
    rndf=13*13*13*13;
    rndf=rndf*rndf*rndf*13;
    rnd=0x849178L;
  }
  else {
    rndf=69069; //3*7*11*13*23
    rnd=0x234571L;
  }
  for (i=0;i<1000;i++)
    rnd=rnd*rndf+1;
  //printf("rnd is %lu \n",rnd); // 13039344770207193520
  //printf("rndf is %lu",rndf);  // 302875106592253

  //all of the below (rz, scfound, scnhelp, schelp) are arrays of length hlength
  check_alloc(rz=(double*)malloc(sizeof(double)*hlength));
  check_alloc(scfound=(long*)malloc(sizeof(long)*hlength));
  check_alloc(scnhelp=(long*)malloc(sizeof(long)*hlength));
  check_alloc(schelp=(double*)malloc(sizeof(double)*hlength));

  //rz = array of length hlength, big number divided by maximum big number
  //from stackoverflow https://stackoverflow.com/questions/43196824/declaring-ulong-max-in-c
  //   "ULONG_MAX is not a type, it's the maximum value allowed for an unsigned long type,
  //   typically defined as something like:"
  //   #define ULONG_MAX 0xFFFFFFFFUL
  
  for (i=0;i<hlength;i++){
    rz[i]=(double)(rnd=rnd*rndf+1)/ULONG_MAX; //random number between 0 and 1 (although
                                              //actually deterministic, not random? "random" indices
                                              //will always be the same if the array to be shuffled
                                              //is the same length)
  }
  
  //SCBOX = "size of the box for the scramble routine" = 4096
  //scbox = array of length SCBOX

  // populate scbox array with -1s
  for (i=0;i<SCBOX;i++)
    scbox[i]= -1;

  // sceps=(double)SCBOX-0.001 = 4095.999
  for (i=0;i<hlength;i++) {
    
    // m is a random integer between 0 and 4095, inclusive
    // scbox1 is SCBOX-1 = 4095
    
    m=(int)(rz[i]*sceps)&scbox1; //bitwise AND with scbox1 = 111111111

    // scfound's ith entry points to scbox's mth entry
    scfound[i]=scbox[m];

    //but now scbox's mth entry equals i
    //so scbox becomes an array of length 4096 populated 
    // by random integers between 0 and 4095 inclusive
    // but also by -1s in (4095 - hlength) of its entries 
    scbox[m]=i;
  }


  //loop through scbox array
  for (i=0;i<SCBOX;i++) {
    scnfound=0;
    element=scbox[i];

    // for elements that do not equal -1 (there are hlength of these)
    while(element != -1) {
      // initially:
      // scnhelp[0] = element
      // but on later loops:
      // scnhelp[1] = element, etc
      scnhelp[scnfound]=element;

      // (scnfound + 1)th entry of schelp = "element"th entry of rz
      // so the first time this loop executes, we have e.g. 
      // schelp[1] = rz[3372]
      // element = scfound[3372]
      // then
      // schelp[2] = rz[2704]
      // element = scfound[2704]
      // etc until we get something like:
      // schelp[3] = rz[1995]
      // element = scfound[1995] = -1 , at which point loop breaks 

      //this line also increments scnfound; if it was 0 above it is now 1 after this line
      //(and will stay 1 if the loop repeats)
      schelp[scnfound++]=rz[element];
      element=scfound[element];

      //this while loop ends when element does equal -1. so the point of it
      //is to populate scnhelp with "element"s not equal to -1
      //and to populate schelp with rz["element"s] where "element" not equal to -1
      //(but only the first couple of entries of scnhelp and schelp?)
    }
        
    // scan through elements of schelp and swap them
    for (j=0;j<scnfound-1;j++)
      for (k=j+1;k<scnfound;k++)
        if (schelp[k] < schelp[j]) {
          swap=schelp[k];
          schelp[k]=schelp[j];
          schelp[j]=swap;
          lswap=scnhelp[k];
          scnhelp[k]=scnhelp[j];
          scnhelp[j]=lswap;
        }
    //use this to scramble elements of scr
    for (j=0;j<scnfound;j++)
      scr[allscr+j]=scnhelp[j];

    //allscr counts up to hlength
    allscr += scnfound;

  }

  free(rz);
  free(scfound);
  free(schelp);
}

//count nearest neighbors to populate found[1:][:] 
//the distance computed between points is the Chebyshev distance,
//i.e. max{|x_i - x_j|} for vector elements i, jf
void make_c2_dim(int n)
{
  char small;
  long i,j,k,x,y,i1,i2,j1,element,n1,maxi,count,hi;
  double *hs,max,dx;
  //hs is an array of length (EMBED*DIM)
  //= an array of length (10*1)= (10,) for our purposes
  check_alloc(hs=(double*)malloc(sizeof(double)*EMBED*DIM));
  n1=scr[n];

  count=0;
  for (i1=0;i1<EMBED;i1++) {
    i2=i1*DELAY;
    for (j=0;j<DIM;j++){
      //hs[count++] = series[0][scr[n] + current (embedding dim * DELAY)]
      hs[count++]=series[j][n1+i2]; //"count" increments after array entry is assigned,
                                    // because it's "count++" and not "++count"

      //so hs[0] = series[0][scr[n] + 0*DELAY]
      //   hs[1] = series[0][scr[n] + 1*DELAY], ...
      //...hs[9] = series[0][scr[n] + 9*DELAY]
    }
  }
  //count is now 10 because it has incremented every time i1
  // increases, up to EMBED=10
  
  //locations in the box
  //recall EPSMAX defaults to the range of the time series
  //imax = NMAX-1 = 255
  
  x=(int)(hs[0]*epsinv*NMAX)&imax; // x = hs[0]/EPSMAX (imax = 0; bitwise "and" in effect but doesn't change anything)
  y=(int)(hs[1]*epsinv*NMAX)&imax; // y = hs[1]/EPSMAX

  //check elements in all boxes
  //possible to edit the range of this loop to exclude boxes which are
  //nearer/farther than the scale of interest
  for (i1=0;i1<=imax;i1++) {
    i2=i1&imax;
    for (j1=0;j1<=imax;j1++) {
      element=box[i2][j1&imax];

      //while there are elements in this box
      while (element != -1) {
        //if safely outside the Theiler window:
        if (labs((long)(element-n1)) > MINDIST) {
          count=0;
          max=0.0;
          maxi=howoften1;
          small=0;
          for (i=0;i<EMBED;i++) {
            hi=i*DELAY;
            for (j=0;j<DIM;j++) {
              //dx = distance in 1D between hs[count] and series[0][thisBoxIdx + i*DELAY]
              //               i.e. between series[0][scr[n] + count*DELAY] and series[0][thisBoxIdx + i*DELAY]
              dx=fabs(hs[count]-series[j][element+hi]);

              //if dx <= range of time series, then:
              if (dx <= EPSMAX) {

                //first loop: if dx > 0;
                //subsequent loops: if dx exceeds earlier dxs,
                //  i.e. dx becomes the max over all 1D distances between
                //  elements of the delay vectors
                // (because we're computing the Chebyshev distance!)

                //if dx > max, new pair to index
                if (dx > max) {
                  max=dx;

                  //how high up to count in log space
                  if (max < EPSMIN) {
                    //if dx < minimum length scale of interest, we'll add 
                    // this pair to every column of found[count]
                    maxi=howoften1;
                  }

                  //else, if dx > minimum length scale of interest,
                  // we'll only add this pair to columns 0 through maxi
                  // of found[count], where maxi corresponds to the index most closely
                  // matching distance dx in log space
                  else {
                    //recall lneps = log(EPSMAX)
                    //recall lnfac = distance in log space between choices of ball size
                    maxi=(lneps-log(max))/lnfac;
                  }
                }

                //found is an array of size (DIM*EMBED, HOWOFTEN) = default (1*10, 100)
                // here we're indexing into the DIM*EMBED dimension with "count"

                //don't do anything to first row of found, i.e. found[0]--
                // that will be filled in by the make_c2_1 function below.
                //for subsequent rows found[count], add 1 "near neighbor found"
                // to every found[count][k] where k <= the index corresponding
                // to distance dx in log space (i.e. dx becomes the radius of our ball)

                if (count > 0)
                  for (k=imin;k<=maxi;k++)
                    found[count][k] += 1.0;
              }
              //else, dx > max range of interest, so stop
              else {
                small=1;
                break;
              }

              count++;

            }
            if (small)
              break;
          }
        }
        element=list[element];
      }
    }
  }
  free(hs);
}

//populate found[0]
void make_c2_1(int n)
{
  int i,x,i1,maxi;
  long element,n1;
  double hs,max;
  
  n1=scr[n];
  hs=series[0][n1];
  
  x=(int)(hs*epsinv*NMAX)&imax;
  
  //exactly the same calculation as make_c2_dim, but only in 1 dimension
  //and results are stored in found[0]
  //notice no delay time involved here at all; we're computing distances
  //between time series points, not between elements of delay vectors
  for (i1=0;i1<=imax;i1++) {
    element=boxc1[i1&imax];
    while (element != -1) {
      if (labs(element-n1) > MINDIST) {
        max=fabs(hs-series[0][element]);
        if (max <= EPSMAX) {
          if (max < EPSMIN)
            maxi=howoften1;
          else
            maxi=(lneps-log(max))/lnfac;
          for (i=imin;i<=maxi;i++)
            found[0][i] += 1.0;
        }
      }
      element=listc1[element];
    }
  }
}

int main(int argc,char **argv)
{
  char smaller,stdi=0;
  FILE *fout,*fstat;
  char *outd1,*outc1,*outh1,*outstat;
  int maxembed;
  long i1,j1,x,y,sn,n,i,j,n1,n2;
  long *oscr;
  long lnorm;
  double eps,*epsm,EPSMAX1,maxinterval;
  time_t mytime,lasttime;
  
  //print function help if -h flag is passed
  if (scan_help(argc,argv)) 
    show_options(argv[0]);
  
  //read in other arguments
  scan_options(argc,argv);

  //show function's "what I do" statement
  #ifndef OMIT_WHAT_I_DO
    if (verbosity&VER_INPUT)
      what_i_do(argv[0],WID_STR);
  #endif

  //get data file
  infile=search_datafile(argc,argv,NULL,verbosity);
  if (infile == NULL)
    stdi=1;
  //figure out where to write output (will be a temporary file when called from pytisean)
  if (FOUT == NULL) {
    if (!stdi) {
      //see ./routines/check_alloc.c --- checks if there's enough memory for this
      check_alloc(FOUT=calloc(strlen(infile)+1,(size_t)1));
      strcpy(FOUT,infile);
    }
    else {
      check_alloc(FOUT=calloc((size_t)6,(size_t)1));
      strcpy(FOUT,"stdin");
    }
  }
  //read appropriate columns from data file (see ./routines/get_multi_series.c)
  //store the length of time series in the "length" variable
  if (column == NULL)
    series=(double**)get_multi_series(infile,&length,exclude,&DIM,"",dimset,verbosity);
  else
    series=(double**)get_multi_series(infile,&length,exclude,&DIM,column,dimset,verbosity);

  //renormalize the data to the interval [0,1] if -E flag is passed
  //see ./routines/rescale_data.c
  if (rescale_set) {
    for (i=0;i<DIM;i++)
      rescale_data(series[i],length,&min,&interval);
    maxinterval=1.0;
  }
  //else, figure out from the time series:
  // "min" = minimum value of the time series
  // "interval" = range of the time series
  // "maxinterval" = range of the time series too (?)
  else {
    maxinterval=0.0;
    for (i=0;i<DIM;i++) {
      min=interval=series[i][0];
      for (j=1;j<length;j++) {
        if (min > series[i][j])
          min=series[i][j];
        if (interval < series[i][j])
          interval=series[i][j];
        }
      interval -= min;
      if (interval > maxinterval)
        maxinterval=interval;
    }
  }
  //"EPSMIN" and "EPSMAX" are the minimum and maximum length scales
  // over which d2 will be calculated, defaulting to range/1000 and range (which are set here.) 
  // (Can also be set by the user with the -r and -R flags.)
  if (!eps_max_set)
    EPSMAX *= maxinterval;
  if (!eps_min_set)
    EPSMIN *= maxinterval;

    
  //EPSMAX will have the value abs(EPSMAX) if abs(EPSMAX)<maxinterval, and the value
  //maxinterval otherwise.
  EPSMAX=(fabs(EPSMAX)<maxinterval) ? fabs(EPSMAX) : maxinterval;

  //EPSMIN will have the value abs(EPSMIN) if abs(EPSMIN)<EPSMAX, and the value
  //EPSMAX/2 otherwise.
  EPSMIN=(fabs(EPSMIN)<EPSMAX) ? fabs(EPSMIN) : EPSMAX/2.;
  EPSMAX1=EPSMAX;

  //HOWOFTEN is the number of length scales at which the correlation sum is computed,
  // defaulting to 100 (but can be set by the user with the # flag)
  howoften1=HOWOFTEN-1;

  //DIM and EMBED are set with the -M flag. DIM is the number of components (defaults to 1)
  // and EMBED is the maximum embedding dimenson (defaults to 10) 
  maxembed=DIM*EMBED-1;

  //allocate appropriate names and places for the function outputs
  //TKTK may need to add another one here to output the nearest neighbor distances
  check_alloc(outd1=(char*)calloc(strlen(FOUT)+4,(size_t)1));
  check_alloc(outc1=(char*)calloc(strlen(FOUT)+4,(size_t)1));
  check_alloc(outh1=(char*)calloc(strlen(FOUT)+4,(size_t)1));
  check_alloc(outstat=(char*)calloc(strlen(FOUT)+6,(size_t)1));
  strcpy(outd1,FOUT);
  strcpy(outc1,FOUT);
  strcpy(outh1,FOUT);
  strcpy(outstat,FOUT);
  strcat(outd1,".d2");
  strcat(outc1,".c2");
  strcat(outh1,".h2");
  strcat(outstat,".stat");
  //see ./routines/test_outfile.c
  test_outfile(outd1);
  test_outfile(outc1);
  test_outfile(outh1);
  test_outfile(outstat);

  //check if there's enough memory
  check_alloc(list=(long*)malloc(length*sizeof(long)));
  check_alloc(listc1=(long*)malloc(length*sizeof(long)));

  //make sure the delay vector isn't too long for the time series
  if ((long)(length-(EMBED-1)*DELAY) <= 0) {
    fprintf(stderr,"Embedding dimension and delay are too large.\n"
      "The delay vector would be longer than the whole series."
      " Exiting\n");
    exit(VECTOR_TOO_LARGE_FOR_LENGTH);
  }

  //check if there's enough memory

  //scr, oscr have the same length as the arrays internal to scramble(),
  // which is length-((EMBED-1)*DELAY) = number of delay vectors if m=EMBED
  //DIM*EMBED = array of length (number of components * max embedding dim) 
  check_alloc(scr=(long*)malloc(sizeof(long)*(length-(EMBED-1)*DELAY)));
  check_alloc(oscr=(long*)malloc(sizeof(long)*(length-(EMBED-1)*DELAY)));

  //found is an array of shape (DIM*EMBED, HOWOFTEN)
  //i.e. (1*10, 100)
  check_alloc(found=(double**)malloc(DIM*EMBED*sizeof(double*)));

  //each row in found will be of length 100
  for (i=0;i<EMBED*DIM;i++)
    check_alloc(found[i]=(double*)malloc(HOWOFTEN*sizeof(double)));

  //norm = array of length 100 (all entries set to zero in next loop)
  check_alloc(norm=(double*)malloc(HOWOFTEN*sizeof(double)));
  //epsm = length scales equally log-spaced, length 100
  check_alloc(epsm=(double*)malloc(HOWOFTEN*sizeof(double)));
  
  epsinv=1.0/EPSMAX;

  //(EPSMAX/EPSMIN) ^ (1/99) = how far apart the length scales will be in log space
  // so that there can be 100 length scales, equally log spaced
  epsfactor=pow(EPSMAX/EPSMIN,1.0/(double)howoften1);
  lneps=log(EPSMAX);
  lnfac=log(epsfactor);

  epsm[0]=EPSMAX;
  norm[0]=0.0;
  for (i=1;i<HOWOFTEN;i++) {
    norm[i]=0.0;
    epsm[i]=epsm[i-1]/epsfactor;
  }

  imin=0;

  //scramble creates an array scr, which has length (length - (EMBED-1)*DELAY) = hlength
  // and consists of the indices 0 to hlength-1, inclusive, scrambled.
  //note that this isn't a *random* scramble---as long as input hlength
  //is the same, output scr will be the same
  scramble();


  //looping over the number of delay vectors = length-(delay*(m-1))
  for (i=0;i<(length-(EMBED-1)*DELAY);i++){
    oscr[scr[i]]=i; //now we have e.g. scr[0] = 3078; oscr[3078] = 0
  }

  // DIM and EMBED are set with the -M flag. DIM is the number of components (defaults to 1)
  // and EMBED is the maximum embedding dimenson (defaults to 10) 
  // HOWOFTEN is the number of length scales we're trying
  //found is an array of size (DIM*EMBED, HOWOFTEN) = default (1*10, 100)
  for (i=0;i<DIM*EMBED;i++)
    for (j=0;j<HOWOFTEN;j++)
      found[i][j]=0.0;
  
  //nmax = length of array - (tau*9) = confusingly, the minimum number of delay vectors
  // we expect (because EMBED is the maximum number of embedding dimensions we're trying)
  // does this mean for m < EMBED, we're actually throwing away the end of our time series?

  //meanwhile recall NMAX = 256, "Size of the field for box assisted neighbour searching 
  // (has to be a power of 2)"
  nmax=length-DELAY*(EMBED-1);

  //boxc1 is an array of length (256)
  //box is an array of shape (256,256)
  //set all elements in both arrays equal to placeholder value -1
  // for i1 in range(0,256):
  for (i1=0;i1<NMAX;i1++) {
    boxc1[i1]= -1;
    //for j1 in range(0,256):
    for (j1=0;j1<NMAX;j1++)
      box[i1][j1]= -1;
  }

  //store current time in variable lasttime
  time(&lasttime);
  lnorm=0;
  
  //looping over delay vectors
  for (n=1;n<nmax;n++) {
    smaller=0;
    //sn = "scrambled n" I guess
    //   = n-1th "scrambled" index, where the indices in "scr" run from 0 to nmax
    sn=scr[n-1];
    //if time series entries are higher-dimensional than 1 (not the case for our purposes)
    if (DIM > 1) {
      x=(long)(series[0][sn]*epsinv*NMAX)&imax;
      y=(long)(series[1][sn]*epsinv*NMAX)&imax;
    }
    // x is the "sn"th entry in the time series * (1/EPSMAX) 
    //       = ("sn"th entry)/(max length scale for correlation dimension calculation)
    // y is the "sn+DELAY"th entry in the time series/max length scale
    // imax is NMAX-1 = 255
    // doing a bitwise AND operation to put 
    else {
      //not much dynamic range in the white noise time series, so
      //x and y do not change over the course of the whole n loop

      x=(long)(series[0][sn]*epsinv*NMAX)&imax; //the &imax here is a binary AND (not the unary address-of operator)
      y=(long)(series[0][sn+DELAY]*epsinv*NMAX)&imax;

    }

    //list, listc1 are both arrays of the same length as the time series
    //first loop: list[this loop's sn] = -1
    //subs loops: list[this loop's sn] = last loop's sn
    list[sn]=box[x][y];
    
    //remove a "-1" value from box
    box[x][y]=sn;

    //put a "-1" value into listc1
    listc1[sn]=boxc1[x];

    //remove a "-1" value from boxc1
    boxc1[x]=sn;

    //imin=0 for now
    i=imin;

    //maxembed = DIM*EMBED-1 = (1*10 - 1) = 9
    //MAXFOUND = "maximum number of pairs to be used" = UMAXLONG (i.e. all possible pairs) for my purposes

    //so this next line amounts to while FALSE
    while (found[maxembed][i] >= MAXFOUND) {
      smaller=1;
      //howoften1 = HOWOFTEN - 1 = 100-1 = 99
      if (++i > howoften1)
        break;
    }

    // smaller stays zero for our choice of "all neighbors", 
    // so don't need to worry about this
    if (smaller) {
      imin=i;
      if (imin <= howoften1) {
        EPSMAX=epsm[imin];
        epsinv=1.0/EPSMAX;
        for (i1=0;i1<NMAX;i1++) {
          boxc1[i1]= -1;
          for (j1=0;j1<NMAX;j1++)
            box[i1][j1]= -1;
        }  
        for (i1=0;i1<n;i1++) {
          sn=scr[i1];
          if (DIM > 1) {
            x=(long)(series[0][sn]*epsinv*NMAX)&imax;
            y=(long)(series[1][sn]*epsinv*NMAX)&imax;
          }
          else {
            x=(long)(series[0][sn]*epsinv*NMAX)&imax;
            y=(long)(series[0][sn+DELAY]*epsinv*NMAX)&imax;
          }
          list[sn]=box[x][y];
          box[x][y]=sn;
          listc1[sn]=boxc1[x];
          boxc1[x]=sn;
        }
      }
    }

    //so skip to here
    // if imin <= 99
    // we're still within the n loop (looping over delay vectors)
    if (imin <= howoften1) {
      //lnorm is going to be added to the number of pairs we've counted overall
      //set lnorm equal to our index n (because at maximum we're counting n additional
      //pairs at this iteration of the loop) and we'll decrement it later if 
      //we want to discard some pairs for being within the Theiler window.
      lnorm=n;
      
      //MINDIST is the user-specified Theiler window. Default value is zero.
      //The effect of this block is to eliminate pairs which are nearby
      //neighbors in time from consideration. (We want only nearby neighbors in
      //*phase space*.)
      if (MINDIST > 0) {
        //sn = "scrambled n"? = nth value of scr
        sn=scr[n];

        //if sn-MINDIST (= sn-0 = sn) is >=0, then n1 has the value sn-MINDIST (= sn).
        // otherwise n1 = 0.
        n1=(sn-(long)MINDIST>=0)?sn-(long)MINDIST:0;
        //if (sn+MINDIST < length-(EMBED-1)*DELAY), 
        // i.e. if sn < numDelayVectors, 
        //then n2 = sn+MINDIST.
        //otherwise n2 = length-((EMBED-1)*DELAY)-1,
        //i.e. n2 = numDelayVectors-1
        n2=(sn+MINDIST<length-(EMBED-1)*DELAY)?sn+MINDIST:
        length-(EMBED-1)*DELAY-1;

        // i1 loops from n1 to n2, i.e. (in ideal case) from sn-MINDIST to sn+MINDIST
        // (accounting for the case where we're too close to the edge of the 
        // array of delay vectors.)
        for (i1=n1;i1<=n2;i1++)
          //if oscr[i1] < n, i.e. if the i1th entry of oscr, then we've
          //found a neighbor that's within the Theiler window and we won't count it
          //decrement lnorm so that the number of total pairs we normalize by remains
          //accurate.
          if ((oscr[i1] < n))
            lnorm--;
      }

      //if EMBED*DIM = EMBED*1 > 1:
      if (EMBED*DIM > 1)
        make_c2_dim(n);
      
      make_c2_1(n);

      //recall norm is an array of length (100)
      //add lnorm to every entry in norm
      //ah, is norm truly just for normalization? I think so
      for (i=imin;i<HOWOFTEN;i++)
        norm[i] += (double)(lnorm);
    }
    
    //print status update to stderr
    //and output results of calculation to outstat, outc1, outh1, outd1
    //(recall we're calling from pytisean, so "outfiles" are actually going
    //to be numpy arrays)
    if (((time(&mytime)-lasttime) > WHEN) || (n == (nmax-1)) || (imin > howoften1)) {
      time(&lasttime);

      fstat=fopen(outstat,"w");
      if (verbosity&VER_USR1)
        fprintf(stderr,"Opened %s for writing\n",outstat);
      fprintf(fstat,"Center points treated so far= %ld\n",n);
      fprintf(fstat,"Maximal epsilon in the moment= %e\n",epsm[imin]);
      fclose(fstat);

      // write c2 to file
      fout=fopen(outc1,"w");
      if (verbosity&VER_USR1)
        fprintf(stderr,"Opened %s for writing\n",outc1);
      fprintf(fout,"#center= %ld\n",n);
      for (i=0;i<EMBED*DIM;i++) {
        fprintf(fout,"#dim= %ld\n",i+1);
        eps=EPSMAX1*epsfactor;
        for (j=0;j<HOWOFTEN;j++) {
          eps /= epsfactor;
          if (norm[j] > 0.0)
            fprintf(fout,"%e %e\n",eps,found[i][j]/norm[j]);
        }
        fprintf(fout,"\n\n");
      }
      fclose(fout);

      //write h2 to file
      fout=fopen(outh1,"w");
      if (verbosity&VER_USR1)
        fprintf(stderr,"Opened %s for writing\n",outh1);
      fprintf(fout,"#center= %ld\n",n);
      fprintf(fout,"#dim= 1\n");
      eps=EPSMAX1*epsfactor;
      for (j=0;j<HOWOFTEN;j++) {
        eps /= epsfactor;
        if (found[0][j] > 0.0)
          fprintf(fout,"%e %e\n",eps,-log(found[0][j]/norm[j]));
      }
      fprintf(fout,"\n\n");
      for (i=1;i<DIM*EMBED;i++) {
        fprintf(fout,"#dim= %ld\n",i+1);
        eps=EPSMAX1*epsfactor;
        for (j=0;j<HOWOFTEN;j++) {
          eps /= epsfactor;
          if ((found[i-1][j] > 0.0) && (found[i][j] > 0.0))
            fprintf(fout,"%e %e\n",eps,log(found[i-1][j]/found[i][j]));
        }
        fprintf(fout,"\n\n");
      }
      fclose(fout);

      //write d2 to file
      fout=fopen(outd1,"w");
      if (verbosity&VER_USR1)
        fprintf(stderr,"Opened %s for writing\n",outd1);
      fprintf(fout,"#center= %ld\n",n);
      for (i=0;i<DIM*EMBED;i++) {
        fprintf(fout,"#dim= %ld\n",i+1);
        eps=EPSMAX1;
        for (j=1;j<HOWOFTEN;j++) {
          eps /= epsfactor;
          if ((found[i][j] > 0.0) && (found[i][j-1] > 0.0))
            fprintf(fout,"%e %e\n",eps,log(found[i][j-1]/found[i][j]/norm[j-1]*norm[j])/lnfac);
        }
        fprintf(fout,"\n\n");
      }
      fclose(fout);

      //if imin > howoften1, end program early. otherwise end when n loop is finished
      if (imin > howoften1)
        exit(0);
    }
  }


  //free all arrays
  if (infile != NULL)
    free(infile);
  
  free(outd1);
  free(outh1);
  free(outc1);
  free(outstat);
  free(list);
  free(listc1);
  free(scr);
  free(oscr);
  free(norm);
  free(epsm);

  for (i=0;i<EMBED*DIM;i++)
    free(found[i]);
  
  free(found);
  
  for (i=0;i<DIM;i++)
    free(series[i]);
  
  free(series);

  return 0;
}
