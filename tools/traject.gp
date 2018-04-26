set terminal svg size 640,480 noenhance

set output ofname

set style data lines

set xlabel "Time [s]"
set ylabel "State"

stats ifname using 1 nooutput
columns = STATS_columns
blocks = STATS_blocks-1

## Solution of plotting only last occurance of each block
## got from StackOverflow:
## https://stackoverflow.com/questions/49921097/gnuplot-how-to-plot-only-last-occurance-of-block-with-repeating-y-values

array signatures[blocks]
do for [b=0:blocks-1] {
  stats ifname index b using 1 nooutput

  #For each block, generate an identifier based on which we will decide if two
  #blocks are "duplicit" or not. In this particular case, consider the minimum
  #and maximum to 3 decimal digits. Due to the character of the technique used
  #below, this identifier should be a valid Gnuplot variable name.
  signatures[b+1] = sprintf("block_%d_%d", STATS_min*1000, STATS_max*1000)
}

#this array marks if a block should be ignored or not.
array ignore[blocks]

#Process blocks in reverse order and for each of them, check if the given
#signature has been already seen or not. If yes, it means that there is
#a more recent equivalent block in the data and the current block should
#be thus ignored. In order to check if a signature has been already seen,
#we set a corresponding variable and then test its existence via exists().
do for [b=blocks-1:0:-1] {
  signature = signatures[b+1]
  eval sprintf("ignore[%d] = exists(\"%s\");%s = 1;", \
               b+1, signature, signature);
}

ymax = -1e30
do for [i=2:columns] {
    stats ifname using i nooutput
    ymax = (ymax > valid(STATS_max)) ? ymax : STATS_max
}

set y2range [0:ymax]

plot for [j=2:columns] for [b=0:blocks-1] ifname index b \
  using 1:(ignore[b+1] ? NaN : column(j)) lt (j-1) \
  title b==0 ? columnhead(j) : "", \
for [b=0:blocks-1] "" index b \
  using 1:(ignore[b+1] ? NaN : column(0) == 1 ? ymax : NaN) \
  axes x1y2 with impulse notitle \
  lc black lw 0.5 dashtype 2
