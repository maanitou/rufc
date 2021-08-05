path <- '/home/maanitou/programming/fsharp/rufc/Samples/schrodinger/'

content_f <- read.table(paste(path, 'output_schrodinger_forward.txt', sep=""))
content_b <- read.table(paste(path, 'output_schrodinger_backward.txt', sep=""))

factor <- 1000000

Xf <- sapply(content_f, function(x) as.numeric(x)/factor)
Xb <- sapply(content_b, function(x) as.numeric(x)/factor)

par(mfrow=c(1,1))

plot(1:128, Xf[1,], type='l',  xlim=c(0,256), ylim=c(min(Xf),max(Xf)))
lines(1:128, Xf[2,], type='l')
lines(129:256, Xb[1,], type='l')
lines(129:256, Xb[2,], type='l')

for (i in 0:(nrow(Xf)/2-1)) {
  lines(1:128, Xf[2*i+1,], type='l', col='red', xlim=c(0,256), ylim=c(min(Xf),max(Xf)))
  lines(1:128, Xf[2*i+2,], type='l', col='black')
  lines(129:256, Xb[2*i+1,], type='l', col='red')
  lines(129:256, Xb[2*i+2,], type='l', col='black')
  #Sys.sleep(1)
}

#pdf(file="/home/maanitou/Desktop/PAT_2021/project/schrodinger.pdf", width=8, height=4)
par(mfrow=c(3,4), oma=c(0,0,0,0), mar=c(.5,.5,.5,.5))
  for (i in c(seq(0,999,91),999)) {
  #for (i in c(seq(0,4999,455),4999)) {
  #for (i in c(seq(0,1999,182),1999)) {
  plot(1:128, Xf[2*i+1,], type='l', col='black',
    xlim=c(0,256), ylim=c(min(Xf),max(Xf)),
    xlab="", ylab="", xaxt='n', yaxt='n')
  lines(1:128, Xf[2*i+2,], type='l', col='red')
  lines(129:256, Xb[2*i+1,], type='l', col='red')
  lines(129:256, Xb[2*i+2,], type='l', col='black')
  abline(v=128, lty=2)
}
#dev.off()