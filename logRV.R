
# A Bayesian Semi-parametric (HAR-DPM) Model for Realized Volatility:

# In this code, we use the Heterogeneous Autoregressive (HAR) model of realized volatility, 
# combined with Bayesian inference as well as Markov chain Monte Carlo method’s to estimate 
# the innovation density of the daily realized volatility. A Dirichlet process (DP) is used as 
# the prior in a countably infinite mixture (M) model. The semi-parametric model provides a 
# robust alternative to the models used in the literature.

# Please refer to https://macsphere.mcmaster.ca/bitstream/11375/13515/1/fulltext.pdf for detailed information.

#libraries
{ 
  library(Matrix)
  library(MCMCpack)
  library(mvtnorm)
  library(stats)
}

# Import Data 
{
  RV <- read.table("/coding/data.txt")[,5]
  #descripetion: date, return (5min) close-to-close 4pm, return from daily data, RV, RV1, RV2, RV3
  logRV <- log(RV)
  n <- length(RV)
}

# function to return a matrix with row = n, and column = 3 (used for estimation of beta)
find_OLSX<-function(logRV){
  
  OLSX <- matrix(rep(0,(n)*3),nrow=(n),ncol=3,byrow = TRUE)
  
  for (i in 1:4){ OLSX[i,] <- cbind(logRV[i],0,0) }
  
  for (i in 5:21){
    weeklogRV  <- mean(logRV[(i-4):i])
    OLSX[i,] <- cbind(logRV[i],weeklogRV,0)
  }
  
  for (i in 22:(n)){
    weeklogRV  <- mean(logRV[(i-4):i])
    monthlogRV <- mean(logRV[(i-21):i])
    OLSX[i,] <- c(logRV[i],weeklogRV,monthlogRV)
  }
  
  OLSX 
}

# Initial guesses
{
  u <- c(rep(0.007,n/2),rep(0.009,n/2))
  V <- c(rep(0.5,n/2),rep(1.5,n/2))
  s <- c(rep(1,n/2),rep(2,n/2))  
  meanBeta0 <- c(0,0,0)
  varBeta0  <- 10*diag(3)
  Beta0  <- meanBeta0 + t(chol(varBeta0)) %*% rnorm(3)
  OLSX <- find_OLSX(logRV)
  y    <- c(logRV[1],logRV[2:n]- OLSX %*% Beta0)
  mean(y)
  var(y)
  phi   <- cbind(u,V)
  theta <- unique(phi)
  n_u <-theta[,1]
  n_V <-theta[,2]
  n_theta <- c(n/2,n/2)
  k <- length(unique(u))
}

##initial parameters
{
  ss    <- 4
  S     <- 4
  m     <- 0   ##mu_mean
  tau   <- 10
  S     <- S +(y-m)^2/(1+tau)   
  X     <- tau/(1+tau)
  x     <- (m+tau*y)/(1+tau)
  M     <- (1+tau)*S/ss
  c_s   <- gamma((1+ss)/2)*(gamma(ss/2)^(-1))*ss^(-0.5)
  alpha <- 0.5
  
  v_h <- 1/2
  s_h <- 1/2
  m   <- 0  ## mu_mean
  tau <- 10*0.1
  
}

#Autocorrelation and Time series plot
{
  Y <- 1:n
  plot(Y,y,type="l")
  title("Historical graph for daily return", xlab = "08/05/1997 to 05/15/2012", ylab = "daily return")
  
  ts.plot(y) 
  title(sub="Figure 1.0: Historical graphfor daily return")
  acf(y)
  title(sub="Figure 1.1: ACF plot with original data")
  
}

# gives s,n_theta, find s
find_s <- function(a,b){  
  n   <- length(a)
  n_a <- a
  s   <- rep(1:n)
  count<-rep(1,n)
  for(i in 2:n){  
    if (length(unique(a[i] == a[-i]))==2){
      p <- (which(a[i] == a[-i]))[1]
      if (b[i]== b[p]){     
        n_a[i] <- 0
        n_a[p] <- a[p]
        s[p]   <- nnzero(n_a[1:p[1]])
        s[i]   <- s[p]
        count[i]<-0
        count[p]<-1+count[p]}
    }      
    if (length(unique(a[i]== a[-i]))==1){
      s[i]<-nnzero(n_a[1:i])}
  }     
  cbind(a,b,s,count)
}
# find_s(u,V)

# function to update theta 
update_theta <- function(u,V,y,n_u,n_V,s,ntheta){ ##########,k )
  
  n <- length(y)
  phi <-cbind(u,V)
  
  k<-length(n_u)
  p <- q <- rep(0,k)     #prob of being the j group, j = 1, ..., k      
  for (i in 1:n){
    
    #### intial treatments
    if (ntheta[s[i]]==1){
      if(s[i]!=k){
        ntheta[s[i]]<-ntheta[k]   ## passing the values from k to s[i] th group
        n_u[s[i]]<-n_u[k]
        n_V[s[i]]<-n_V[k]
      }
      ntheta<-ntheta[1:(k-1)]    ## deleting the last entries
      n_u<-n_u[1:(k-1)]
      n_V<-n_V[1:(k-1)]
      s[c(which(s==k))]=s[i] 
      k<-k-1 }
    else {ntheta[s[i]]<- ntheta[s[i]]-1}
    ## the prob of having a new parameter, sum_prob for summing the probabilities.
    prec<-sqrt(v_h/s_h*tau/(1+tau))
    sum_prob<- q0 <- p0 <- alpha*dt((y[i]-m)/prec,v_h)/prec 
    #### here is the most problematic part:  
    
    for (j in 1:k){                ### prob for being j th group 
      q[j]<- ntheta[j]*dnorm(y[i],n_u[j],sqrt(n_V[j]))
      #q[j] <- ntheta[j]*(2*n_V[j])^(-0.5)*exp(-0.5*(y[i]-n_u[j])^2/n_V[j])
      sum_prob<-sum_prob+q[j]
    } # for j 
    
    p0<-q0<- q0/sum_prob             # normalizing p0, q0
    for (j in 1:k){       
      q[j] <- q[j]/sum_prob         # normaling q[j]
      p[j] <- q0 + sum(q[1:j])      # cumulating p[j]  
    }
    
    
    
    deci <- runif(1)                           ### setting a decision number 
    
    if (deci < p0){   ### if it is a observation with new parameter:
      tau_bar<-tau+1                      
      mu_bar<-(tau*m+y[i])/tau_bar
      v_bar<-v_h+1
      s_bar<-s_h+(mu_bar-y[i])^2+(mu_bar-m)^2*tau
      V[i]<-1/rgamma(1,v_bar/2,s_bar/2)
      u[i]<-rnorm(1,mu_bar,sqrt(V[i]/tau_bar))  
      #V[i]<-1/(rgamma(1,(1+ss)/2,S[i]/2))   ######scale in paper = rate in R
      #u[i]<-rnorm(1,x[i],(X*V[i])^0.5)
      n_u <- c(n_u, u[i])      ### adding one more entries
      n_V <- c(n_V,V[i])
      ntheta <- c(ntheta,1)     ### having one more group
      s[i]<-k<-k+1              ### assign it to be the last group
    }
    else {
      if (deci < p[1] & deci >= p0){
        u[i] <- n_u[1]                        ### passing the value to individual u and V 
        V[i] <- n_V[1]
        ntheta[1] <- ntheta[1]+1              ### adding one to the number of the member in the first group
        s[i]<-1                               ### assign the i th element to the first group 
      } ## if deci first group
      else{
        for (j in 2:k){                            #### for other groups
          if (deci < p[j] & deci >= p[j-1]){
            u[i] <- n_u[j]                         ### passing the new values to individual u and V
            V[i] <- n_V[j]
            ntheta[j] <-ntheta[j]+1             ### adding one more member 
            s[i]<-j                                ### assign it to be the last group
            break}  ## if deci the j th group (j>2)
        }  ## for j
      }  ## else 2
    } # else 1 
    
  }# for i
  
  #### data frame output :
  
  data1<- data.frame(u,V,y,s)
  k<-length(n_u)
  data2<-data.frame(n_u,n_V,ntheta)
  c(data1,data2,data.frame(k))
}
# update_theta(u,V,y,theta[,1],theta[,2],s,n_theta) 

# function to sample theta|s,k,y , this is the second step to improve sample efficiency
sample_theta <- function (theta,s,k,y,ntheta){
  ##parameters
  
  n   <- length(y)
  n_u <- theta[,1]
  n_V <- theta[,2]
  for (j in 1:k){
    # i-th obs in each cluster j
    tau_bar <- tau + ntheta[j]
    y_bar   <- sum(y[which(s==j)])/ntheta[j]    #mn1,  y_ bar_j
    u_bar   <- (tau*m + ntheta[j]*y_bar)/(tau+ntheta[j])  #mu bar
    v_h_bar <- v_h + ntheta[j]
    ss1<-sum(y[which(s==j)]^2)- y_bar^2*ntheta[j]   ## ss = mn2 - number*pow( mn1 , 2 );
    s_h_bar <- s_h +ss1 +(u_bar-y_bar)^2*ntheta[j] +(u_bar-m)^2*tau
    n_V[j]  <- 1/(rgamma(1,v_h_bar/2,s_h_bar/2))
    n_u[j]  <- rnorm(1,u_bar,sqrt(n_V[j]/tau_bar))  ######
  } 
  cbind(n_u,n_V)
}
#sample_theta(theta,s,k,y,n_theta)


# function to update beta and y in the HAR-RV Model
update_Beta_y<-function(m_B,v_B,X,y,theta,s){
  u  <- v <- rep(0,n)
  for (i in 1:n){
    u[i] <-theta[s[i],1]
    v[i] <- theta[s[i],2]
  }
  
  XX <- cbind((X[,1]/v),(X[,2]/v),(X[,3]/v))[22:(n-1),]
  YY <- ((logRV-u)/v)[23:n]
  
  varB  <- solve( t(XX) %*% XX + solve(v_B))  
  meanB <- varB %*% (t(XX) %*% YY + solve(v_B) %*% m_B)
  B <- meanB + t(chol(varB)) %*% rnorm(3)
  
  y <- c(logRV[1:22],logRV[23:n] - XX %*% B)
  
  data1 <- data.frame(y)
  data2 <- data.frame(B,meanB,varB)
  c(data1,data2)
}
update_Beta_y(meanBeta0,varBeta0,OLSX,y,theta,s)
  
# function to find the predictive density of y_n+1  (6)
predict_y <- function (theta,y,k,n_theta){
  
  n_u <- theta[,1]
  n_V <- theta[,2]
  sigma <- sqrt( (1/tau+1)* s_h /v_h )
  f1  <- 1/sigma*dt((y-m)/sigma,v_h)*alpha/(alpha+n) 
  f2  <- 0
  for (i in 1:k){
    
    f2 <- f2 + dnorm(y,n_u[i],n_V[i]^(0.5))*n_theta[i]/(alpha+n)
  }
  p <- f1+f2
  p
}
#predict_y(theta,y,k,n_theta)
integrate(function(x){predict_y(theta,x,k,n_theta)},-Inf, Inf)

predict_logRV <- function (theta,k,n_theta,B,X,logRV,s,alpha){
  n <- length(s)
  n_u<-theta[,1]
  n_V<-theta[,2]
  sigma <- sqrt((1/tau+1)*s_h/v_h)
  f1  <- 1/sigma*dt((logRV -  X %*% B  - m)/sigma,v_h)*alpha/(alpha+n) 
  
  f2  <- 0
  for (i in 1:k){
    f2 <- f2 + dnorm(logRV, X %*% B + n_u[i],n_V[i]^(0.5))*n_theta[i]/(alpha+n)
  }
  
  f1 + f2
 
}
predict_logRV(theta,k,n_theta,Beta0,OLSX[n,],0.1,s,alpha)
integrate(function(x){predict_logRV(theta,k,n_theta,Beta0,OLSX[n,],x,s,alpha)},-Inf, Inf)

#function to sample alpha
sample_alpha <- function(alpha, k){
  a   <- 1
  b   <- 4
  eta <- rbeta(1, alpha+1,n)
  pai_eta<-(a+k-1)/((n*(b-log(eta)))+a+k-1)
  p_eta<-runif(1)
  if (p_eta <= pai_eta) {alpha<-rgamma(1,shape=a+k,rate=b-log(eta))}
  if (p_eta >  pai_eta) {alpha<-rgamma(1,shape=a+k-1,rate=b-log(eta))}
  alpha
}
#sample_alpha(0.5,eta,k)

#main loop
{ 
  alpha <- 0.5
  pre_y <- seq(-10,10,20/(n-1))
  NN    <- 10000 #number of iteration
  
  list.s      <- vector("list",NN)
  array.k     <- matrix(rep(0,NN), ncol=NN)
  list.theta  <- vector("list",NN)
  list.y      <- vector("list",NN)
  list.logRV  <- vector("list",NN) 
  array.alpha <- matrix(rep(0,n*NN), ncol=NN)
  list.beta   <- vector("list",NN)
  list.betaM  <- vector("list",NN)
  list.betaV  <- vector("list",NN)
  
  upd         <- update_Beta_y(meanBeta0,varBeta0,OLSX,y,theta,s)
  y           <- upd$y  
  
  

  
  list.betaM[[1]]  <- upd$meanB
  list.betaV[[1]]  <- cbind(upd$X1, upd$X2, upd$X3)
  
  phi             <- unique(cbind(u,V))
  first.data      <- update_theta(u,V,y,phi[,1],phi[,2],s,n_theta)  #first iteration
  
  alpha           <- sample_alpha(alpha,first.data[[8]])
  list.s[[1]]     <- first.data$s
  array.k[1]     <- first.data[[8]]
  list.theta[[1]] <- matrix(c(first.data$n_u,first.data$n_V),ncol=2,nrow=first.data[[8]])
  list.beta [[1]] <- upd$B  
  list.logRV[[1]] <- predict_logRV(list.theta[[1]],first.data[[8]],first.data$ntheta,upd$B,OLSX[n,],pre_y,first.data$s,alpha)
  array.alpha[,1] <- alpha
  
  for (i in 2:NN){

    list.betaM[[i]] <- upd$meanB
    list.betaV[[i]] <- cbind(upd$X1, upd$X2, upd$X3)
    upd             <- update_Beta_y(list.betaM[[i]],list.betaV[[i]],OLSX,y,list.theta[[i-1]],first.data$s)
                                        #m_B,v_B,X,y,logRV,theta,s
    y               <- upd$y 
    
    alpha           <- sample_alpha(alpha,first.data[[8]])
    array.alpha[,i] <- alpha    
    first.data      <- update_theta(first.data$u,first.data$V,y,first.data$n_u,first.data$n_V,first.data$s,first.data$ntheta) 
    list.s[[i]]     <- first.data$s
    array.k[i]     <- first.data[[8]]
    list.theta[[i]] <- matrix(c(first.data$n_u,first.data$n_V),ncol=2,nrow=first.data[[8]])
    list.theta[[i]] <- sample_theta(list.theta[[i]],first.data$s,first.data[[8]],y,first.data$ntheta)
    list.logRV[[i]] <- predict_logRV(list.theta[[i]],first.data[[8]],first.data$ntheta,upd$B,OLSX[n,],pre_y,first.data$s,alpha)
    list.beta[[i]]  <- upd$B
    #print (first.data[[8]]) # value of k
    #print (alpha)
  }
  
  #list.theta
  #list.s
}

#graph of predictive value
{
  nn<-length(pre_y)
  pred_y<-rep(0,nn)
  burn_in<-trunc(NN*0.2)
  
  for (i in burn_in:NN){
    pred_y  <- pred_y + list.logRV[[i]]
    print(head(pred_y))
  }
  

  pred_y <- pred_y/(NN - burn_in +1)

  pre_y  <- pre_y[2:nn]
  pred_y <- pred_y[2:nn]
  
  plot(pre_y,pred_y,type = "l",col="black",xlab="predictive value",ylab="density")
  lines(pre_y,dnorm(pre_y,mean(y),sqrt(var(y))),col = "red")
  legend("topright",legend=c("predictive","normal"),col=c("black","red"),lty=1,lwd=1,cex=1)
  
  plot(pre_y,log(pred_y),type = "l",col="black",xlab="predictive value",ylab="density")
  lines(pre_y,log(dnorm(pre_y,mean(y),sqrt(var(y)))),col = "red")
  title("log of predictive density with 5000 iterations")
  legend("topright",legend=c("predictive","normal"),col=c("black","red"),lty=1,lwd=1,cex=1)
  
  
}



B1<-B2<-B3<- rep(0,NN-1)

for (i in 1:NN){
  B1[i] <- list.beta[[i]][1]
  B2[i] <- list.beta[[i]][2]
  B3[i] <- list.beta[[i]][3]
}


mean(array.k[1,])
var(array.k[1,])
mean(array.alpha[1,])
var(array.alpha[1,])

OLSbeta 
mean(B1)
mean(B1)-1.96*(sqrt(var(B1)))
mean(B1)+1.96*(sqrt(var(B1)))
mean(B2)  
mean(B2)-1.96*(sqrt(var(B2)))
mean(B2)+1.96*(sqrt(var(B2)))
mean(B3)
mean(B3)-1.96*(sqrt(var(B3)))
mean(B3)+1.96*(sqrt(var(B3)))

Beta<-cbind(B1,B2,B3)

var(Beta)
#check beta
#betahat=(t(X)x)^(-1)* t(X)*y
{
  uu<-list.theta[[NN]][,1]
  vv<-list.theta[[NN]][,2]
  s<-list.s[[NN]]
  u<-v<-rep(0,n)
  for (i in 1:n){u[i]<-uu[s[i]];v[i]<-vv[s[i]]}
  OLSXx <- cbind(OLSX[,1]/v,OLSX[,2]/v,OLSX[,3]/v)[22:(n-1),]
  A <- solve(t(OLSXx) %*% OLSXx) %*% t(OLSXx)
  OLSbeta <- solve(t(OLSXx) %*% OLSXx) %*% t(OLSXx)  %*% (((logRV-u)/v)[23:n])
  Y <- var(((logRV-u)/v)[23:n])
  variance <- (A * Y) %*% t(A)
  OLSbeta 
  
  OLSbeta[1]-1.96* sqrt(variance[1,][1])
  OLSbeta[1]+1.96* sqrt(variance[1,][1])
  OLSbeta[2]-1.96* sqrt(variance[2,][2])
  OLSbeta[2]+1.96* sqrt(variance[2,][2])
  OLSbeta[3]-1.96* sqrt(variance[3,][3])
  OLSbeta[3]+1.96* sqrt(variance[3,][3])

  uu<-list.theta[[NN]][,1]
  vv<-list.theta[[NN]][,2]
  s<-list.s[[NN]]
  u<-v<-rep(0,n)
  for (i in 1:n){u[i]<-uu[s[i]];v[i]<-vv[s[i]]}
  OLSXx <- cbind(1/v,OLSX[,1]/v,OLSX[,2]/v,OLSX[,3]/v)[22:(n-1),]
  A <- solve(t(OLSXx) %*% OLSXx) %*% t(OLSXx)
  OLSbeta <- solve(t(OLSXx) %*% OLSXx) %*% t(OLSXx)  %*% (((logRV)/v)[23:n])
  Y <- var(((logRV)/v)[23:n])
  variance <- (A * Y) %*% t(A) 

  OLSbeta[1]-1.96* sqrt(variance[1,][1])
  OLSbeta[1]+1.96* sqrt(variance[1,][1])
  OLSbeta[2]-1.96* sqrt(variance[2,][2])
  OLSbeta[2]+1.96* sqrt(variance[2,][2])
  OLSbeta[3]-1.96* sqrt(variance[3,][3])
  OLSbeta[3]+1.96* sqrt(variance[3,][3])
  OLSbeta[4]-1.96* sqrt(variance[4,][4])
  OLSbeta[4]+1.96* sqrt(variance[4,][4])
}

mean(u)
mean(u)-1.96* sqrt(var(u))
mean(u)+1.96* sqrt(var(u))
