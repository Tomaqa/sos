set terminal svg size 640,480 noenhance

set output ofname

set style data lines

set xlabel "Time [s]"
set ylabel "State"

set key autotitle columnhead

stats ifname using 1 nooutput
columns = STATS_columns
blocks = STATS_blocks

ymin = 1e30
ymax = -1e30
do for [i=2:columns] {
	stats ifname using i nooutput
	ymin = (ymin < valid(STATS_min)) ? ymin : STATS_min
	ymax = (ymax > valid(STATS_max)) ? ymax : STATS_max
}

plot for [j=2:columns] ifname using 1:j, \
  "" using 1:(column(0) == 1 ? ymax : NaN) axes x1y2 with impulse notitle lc black lw 0.75 dashtype 2
