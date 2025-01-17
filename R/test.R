source("./apple.R")
library(readr)

lafile<-function(f){str<-read_file(f);jit(str)}

ncdf<-lafile("../math/ncdf.🍎")
run(ncdf,3);pnorm(3)

chisqcdf<-lafile("../math/chisqcdf.🍎")
run(chisqcdf,2,2);pchisq(2,2)

tcdf<-lafile("../math/tcdf.🍎")
run(tcdf,2,12);pt(2,12)

sliding_mean<-jit("([((+)/x)%ℝ(:x)]\\`7)")
stopifnot(all(run(sliding_mean,seq(0,10,1.0))==c(3,4,5,6,7)))

cat<-jit("[x++(y::Vec n int)]")
stopifnot(all(run(cat,as.integer(c(1,1)),as.integer(c(0,2,3)))==c(1,1,0,2,3)))

any1<-jit("(λa. (λbs. (∨)/ₒ #f bs)`{1∘[2]} (a::M bool))")
stopifnot(all(run(any1,matrix(c(FALSE,FALSE,FALSE,TRUE),2))==c(FALSE,TRUE)))

any<-jit("λbs. (∨)/ₒ #f bs :: bool")
stopifnot(run(any,c(FALSE,FALSE,FALSE,TRUE)))

stopifnot(all(const("re: 2 (even.'irange 0 2 1)")==matrix(c(TRUE,FALSE,TRUE,TRUE,FALSE,TRUE),2,byrow=TRUE)))

isbn<-jit('λxs. ((+)/ (*)`xs (}:(𝔸13⊙7)))|10=0')
stopifnot(run(isbn,as.integer(c(9,7,8,0,5,9,6,5,2,8,1,2,6))));stopifnot(!run(isbn,as.integer(c(9,7,8,1,7,8,8,3,9,9,0,8,3))))
rm(isbn)
gc()

prime_mask<-jit("λN. (λn.¬((∨)/ₒ #f ([(n|x)=0]'(⍳ 2 (⌊(√(ℝn))) 1))))'(irange 2 N 1)")
stopifnot(all(run(prime_mask,9)==c(TRUE,TRUE,FALSE,TRUE,FALSE,TRUE,FALSE,FALSE)))
