path <- '/home/maanitou/programming/fsharp/rufc/Samples/schrodinger/'

content_f <- read.table(paste(path, 'output_schrodinger_forward.txt', sep=""))

factor <- 1000000

Xf <- sapply(content_f, function(x) as.numeric(x)/factor)

par(mfrow=c(1,1))

plot(1:128, Xf[1,], type='l',  xlim=c(0,128), ylim=c(min(Xf),max(Xf)))
lines(1:128, Xf[2,], type='l')

for (i in 1:(nrow(Xf)-1)) {
  plot(1:128, Xf[i,], type='l', col='red', xlim=c(0,128), ylim=c(min(Xf),max(Xf)))
  lines(1:128, Xf[i+1,], type='l', col='black')
  
  #Sys.sleep(0.001)
}