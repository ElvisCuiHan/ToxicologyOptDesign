#
# This is a Shiny web application. You can run the application by clicking
# the 'Run App' button above.
#
# Find out more about building applications with Shiny here:
#
#    http://shiny.rstudio.com/
#

library(shiny)
library(shinyMatrix)
library(shinycssloaders)
library(tidyverse)

#6 sets of Model parameter values
P1=c(-1.250,  0.004 , 1.460 ,-0.007)
P2=c(-1.5,.007,1.70,-0.01)
P3=c(-1.75,.010,2,-0.013)
P4=c(-1.5,.004,1.460,-0.007)
P5=c(-1,.004,2.460,-0.007)
P6=c(-1,.006,3.460,-0.01)
T=rbind(P1,P2,P3,P4,P5,P6)

# Lambda
Lambda = t(as.matrix(c(1/6, 1/6, 1/6, 1/6, 1/6, 1/6)))
colnames(Lambda) = c("P1", "P2", "P3", "P4", "P5", "P6")

generate_header = function(D) {
  hi = "Optimal Design"
  for (i in 1:dim(D)[2]) {
    hi = paste(hi, "\n", "Dose: ", D[1,i], "Weight: ", D[2, i])
  }
  #print(hi)
  return(hi)
}

generate_plot = function(LB=0,UB=10,T,LCp=0.50,weight=0.5,grid=1,r=10, Lambda) {
  ####
  e1=10^-7
  e2=0.01
  n=1
  p1=1
  nit=r
  it=1
  gr=grid
  T=T
  #weight for the D-criterion
  q=weight
  EDp=LCp
  numberrow=nrow(T)
  
  #if(numberrow==1) {Lambda=1} else {
  #  Lambda=rep(1/nrow(T),nrow(T))}
  Lambda = as.vector(Lambda) / sum(Lambda)
  X=c(LB,LB+(UB-LB)/4,LB+2*(UB-LB)/4,LB+3*(UB-LB)/4,UB)
  wX=length(X)
  #print("hii")
  W=rep(1/wX,wX-1)
  #print("hii")
  
  #Information matrix  
  ginv <- function(X, tol = sqrt(.Machine$double.eps)) {
    dnx <- dimnames(X)
    if (is.null(dnx)) 
      dnx <- vector("list", 2)
    s <- svd(X)
    nz <- s$d > tol * s$d[1]
    structure(if (any(nz)) 
      s$v[, nz] %*% (t(s$u[, nz])/s$d[nz])
      else X, dimnames = dnx[2:1])
  }
  I=function(T,X)
  {a=exp(T[1]+T[2]*X)
  b=exp(T[3]+T[4]*X)
  g1=(trigamma(a)-trigamma(a+b))*a^2
  g2=-trigamma(a+b)*a*b
  g3=(trigamma(b)-trigamma(a+b))*b^2
  I1=matrix(c(g1,g2,g2,g3),nrow=2,ncol=2,byrow=F)
  I2=matrix(c(1,X,X,X^2),nrow=2,ncol=2,byrow=F)
  kronecker(I1,I2)}
  upinfor <- function(W,T,X) {
    k = length(X)
    last_infor = I(T,X[k])
    infor = (1 - sum(W)) * last_infor
    for (i in 1:(k - 1)) {
      infor = infor +W[i] * I(T,X[i])
    }
    infor
  }
  
  #First derivative of the EC50 w.r.t parameters
  g=function(q,T){
    #EC50=exp(-(T[3]-T[1])/(T[4]-T[2]))
    f=matrix(c(1/(T[4]-T[2]),(log(1/q-1)-(T[3]-T[1]))/(T[4]-T[2])^2,-1/(T[4]-T[2]),
               (-log(1/q-1)+(T[3]-T[1]))/(T[4]-T[2])^2),nrow=4,ncol=1,byrow=F)
    f}
  
  #g1=g(EDp,P)
  #sensetivity function
  #D-optimality
  ds1=function(T,X,inv) {
    sum(diag((I(T,X)%*%inv)))/4
  }
  #C-optimality
  ds2=function(T,X,inv,g1) {
    sum(diag((I(T,X)%*%inv%*%g1%*%t(g1)%*%inv)))%*%(t(g1)%*%inv%*%g1)^-1
  }
  #First derivative of the D-optimality criterion      
  d1<-function(T,X,XL,inv) {
    sum(diag(inv%*%(I(T,X)-I(T,XL))))
  }
  #Second derivative of the D-optimality criterion
  dd1<-function(T,X1,X2,XL,inv) {
    sum(diag(-inv%*%(I(T,X2)-I(T,XL))%*%inv%*%(I(T,X1)-I(T,XL))))
  }
  #First derivative of the c-optimality criterion for EDp  
  d2<-function(T,X,XL,inv,g1) {
    (-t(g1)%*%inv%*%(I(T,X)-I(T,XL))%*%inv%*%g1)*(t(g1)%*%inv%*%g1)^-1
  }
  #Second derivative of the c-optimality criterion
  dd2=function(T,X1,X2,XL,inv,g1) {
    temp1=(t(g1)%*%inv%*%(I(T,X2)-I(T,XL))%*%inv%*%(I(T,X1)-I(T,XL))%*%
             inv%*%g1+t(g1)%*%inv%*%(I(T,X1)-I(T,XL))%*%inv%*%(I(T,X2)-I(T,XL))%*%
             inv%*%g1)
    
    temp2=-(t(g1)%*%inv%*%(I(T,X1)-I(T,XL))%*%inv%*%g1)*(t(g1)%*%inv%*%g1)^-1*(t(g1)%*%inv%*%(I(T,X2)-I(T,XL))%*%inv%*%g1)
    ((t(g1)%*%inv%*%g1)^-1)*(temp1+temp2)
  }
  #One iteration to run Newton Raphson to get optimal weights   
  Dc_weight<-function(L,W,T,X,d) {
    p=length(W)
    k=length(X)
    np=nrow(T)
    inv=array(rep(0,16), c(4,4,np))
    #print("hi")
    for(i in 1:np)
    {inv[,,i]=solve(upinfor(W,T[i,],X))}
    #print("hii")
    
    f1=rep(0,p)
    f2=matrix(c(rep(f1,p)),nrow=p,ncol=p,byrow=F)
    for (i in 1:p) {
      sumd1=rep(0,np)
      for(j in 1:np){
        #print("hi")
        sumd1[j]=L[j]*(weight*d1(T[j,],X[i],X[k],inv[,,j])/4-(1-weight)*d2(T[j,],X[i],X[k],inv[,,j],g(LCp,T[j,])))}
      f1[i]=sum(sumd1)}
    
    for(i in 1:p) {
      for(j in 1:p) {
        sumdd1=rep(0,np)
        for(l in 1:np){
          sumdd1[l]=L[l]*(weight*dd1(T[l,],X[i],X[j],X[k],inv[,,l])/4-(1-weight)*dd2(T[l,],X[i],X[j],X[k],inv[,,l],g(LCp,T[l,])))}
        f2[i,j]=sum(sumdd1)}
    }
    #print(f2)
    newweight=W-d*(f1%*%ginv(f2))
    #print("hiii")
    newweight
  }
  S_weight<-function(X,T,L) {
    diff=10
    k=length(X)
    W=rep(1/k,k-1)
    while(diff>e1) {
      d=1
      #print("test0")
      NW=Dc_weight(L,W,T,X,d)
      #print("test01")
      minW=min(min(NW),1-sum(NW))
      #print(NW)
      while(minW<0 & d>.0001) {
        d=d/2
        #print("test1")
        NW=Dc_weight(L,W,T,X,d)
        #print("test2")
        minW=min(min(NW),1-sum(NW))
      }
      NW=c(NW,1-sum(NW))
      n=length(NW)
      minW=min(NW)
      diff=max(abs(W-NW[1:n-1]))
      if (abs(minW)<.0000001||minW<0) {
        for(i in 1:n) {
          if (NW[i]==minW)NW[i]=0
        }
        
      }
      
      D=rbind(X,NW)
      for (i in 1:n) {
        if (D[2,i]==0) D[,i]=NA
      }
      X=D[1,]
      W=D[2,]
      X=na.omit(X)
      W=na.omit(W)
      k=length(X)
      W=W[1:k-1]
    }
    W=c(W,1-sum(W))
    D=rbind(X,W)
    D
    
  }
  #print("test")
  # Run V-algorithm to get initial design points
  while(n<r){
    x=seq(from=LB,to=UB,grid)
    nL=length(Lambda)
    n1=length(x)
    ds=rep(0,n1)
    
    inv=array(rep(0,16), c(4,4,nL))
    #print(4)
    for(i in 1:nL)
    {inv[,,i]=solve(upinfor(W,T[i,],X))}   		
    for (i in 1:n1) {
      sumds1=rep(0,nL)	
      for(j in 1:nL){
        sumds1[j]=Lambda[j]*(weight*ds1(T[j,],x[i],inv[,,j])+(1-weight)*ds2(T[j,],x[i],inv[,,j],g(LCp,T[j,])))}
      ds[i]=sum(sumds1)
    }
    newX=x[which.max(ds)]
    #newX=round(newX[1],2)
    newds=max(ds)
    an=1/(n+1)
    p<-abs(newds-1)
    X=c(X,newX)
    W=c(W,1-sum(W))
    newW=(1-an)*W
    W=newW
    #print(p)
    n=n+1
  }
  #print("hi")
  
  r=length(X)
  X=unique(X[(r-wX):r])
  X=sort(X,decreasing=F)
  #print("hi")
  while(p1>e2) {
    print("Still running, please be patient ...")
    x=seq(LB,UB,grid)
    n1=length(x)
    nL=length(Lambda)
    ds=rep(0,n1)
    #print("hi")
    D=S_weight(X,T,Lambda)
    #print("hi")
    X=D[1,]
    k=length(X)
    W=D[2,1:k-1]
    inv=array(rep(0,16), c(4,4,nL))
    #print("hi")
    for(i in 1:nL)
    {inv[,,i]=solve(upinfor(W,T[i,],X))}
    for (i in 1:n1) {
      sumds1=rep(0,nL)	
      for(j in 1:nL){
        sumds1[j]=Lambda[j]*(weight*ds1(T[j,],x[i],inv[,,j])+(1-weight)*ds2(T[j,],x[i],inv[,,j],g(LCp,T[j,])))}
      ds[i]=sum(sumds1)
    }
    #print("hi")
    newX=x[which.max(ds)]
    newds=max(ds)
    X=c(X,newX)
    X=sort(X,decreasing=F)
    X=unique(X)
    newp<-abs(newds-1)
    #print("hi")
    if(abs(newp-p1)<.0000001)   newp=10^-20
    if(it>20)   newp=10^-20
    p1=newp
    it=it+1
    #print(p1)
  }
  #print("hi")
  #Verification of the optimal design	
  X=D[1,]
  n=length(X)
  W=D[2,1:n-1]
  x=seq(LB,UB,grid)
  nL=length(Lambda)
  n1=length(x)
  ds=rep(0,n1)
  inv=array(rep(0,16), c(4,4,nL))
  for(i in 1:nL)
  {inv[,,i]=solve(upinfor(W,T[i,],X))}
  for (i in 1:n1) {
    sumds1=rep(0,nL)	
    for(j in 1:nL){
      sumds1[j]=Lambda[j]*(weight*ds1(T[j,],x[i],inv[,,j])+(1-weight)*ds2(T[j,],x[i],inv[,,j],g(LCp,T[j,])))}
    ds[i]=sum(sumds1)
  }
  
  Dose=round(X,3)
  Weight=round(W,3)
  Weight=c(Weight,1-sum(Weight))    
  D=rbind(Dose,Weight)
  
  ca = c()
  for (i in Dose) {
    ca = c(ca, ds[which.max(x == round(i))])
  }
  
  g = ggplot() + 
    geom_line(aes(x=x, y=ds), cex=1., color="blue") +
    geom_point(aes(x=Dose, y=ca), cex=2.4, color="red") +
    ylab("Sensitivity function") + xlab("Dose Level") +
    #ggtitle(paste("Dose: ", t(D[1,]), "  Weight: ", D[2,]))
    ggtitle(generate_header(D)) +
    xlim(LB, UB) +
    annotate("text", x = (quantile(x, 0.25)), y = min(ds), #yend = max(ds)+0.01,
             colour = "black", label = c("Blue lines: sensitivity function. Red points: design points.")) +
    theme(plot.background = element_rect(fill = "pink")) 
    
  #Print optimal design rescaled on original dose level
  cat(format("Dc-optimal design:", width=80),"\n")
  print(D)
  return(g)
}

# Define UI for application that draws a histogram
ui <- fluidPage(
  style="font-family: 'Montserrat', sans-serif;",
  withMathJax(),
  # Application title
  fluidRow(style="background-color:#FFD700;",
           fluidRow(style="margin-right:8%;margin-left:8%;background-color:#FFD700;",
                    tags$h2(style="text-align:center;", 
                            tags$b('A Model-based Approach to Designing 
                                   Developmental Toxicology Experiments 
                                   using Sea Urchin Embryos')),
                    tags$br(),
                    #tags$h4(style="text-align:center;", 'Michael D. Collins', tags$sup('a'), 
                    #        ', Seung Won Hyun',  tags$sup('b'),  
                    #', Heng-Chin Tung', tags$sup('c'), 
                    #        'and Weng Kee Wong',  tags$sup('c')
                    #),
                    #tags$br(),
                    #tags$h4(style="text-align:center;", tags$sup('a'), 'Department of Environment Health Sciences and Molecular Toxicology Interdepartmental Program, University of California, Los Angeles, CA 90095, USA'), 
                    #tags$h4(style="text-align:center;", tags$sup('b'), 'Research Biostatistics, Johnson and Johnson Medical Devices, Irvine, CA 92618, USA'), 
                    #tags$h4(style="text-align:center;", tags$sup('c'), 
                    #        'Department of Biostatistics, Fielding School of Public Health, UCLA, Los Angeles, CA 90095, USA')
           )
  ),
  
  tags$h5('This app implements the PSO algorithm for finding locally dual optimal 
          design for the developmental toxicology experiments in the paper and the
          dual objective function shown below. There is one design variable, x, 
          the dose level. The design space is the positive half-line. Users can specify 
          their own inputing parameters in the left part of the implementation panel.'),

  fluidRow(style="background-color:#FFA700;",
           fluidRow(style="margin-right:8%;margin-left:8%;background-color:#FFA700;",
                    tags$h2(style='margin-right:1%;margin-left:1%;', 
                            tags$b('A Recap of Dual Optimal Design')),
                    tags$br(),
                    #tags$h4(style="text-align:center;", 'Michael D. Collins', tags$sup('a'), 
                    #        ', Seung Won Hyun',  tags$sup('b'),  
                    #', Heng-Chin Tung', tags$sup('c'), 
                    #        'and Weng Kee Wong',  tags$sup('c')
                    #),
                    #tags$br(),
                    #tags$h4(style="text-align:center;", tags$sup('a'), 'Department of Environment Health Sciences and Molecular Toxicology Interdepartmental Program, University of California, Los Angeles, CA 90095, USA'), 
                    #tags$h4(style="text-align:center;", tags$sup('b'), 'Research Biostatistics, Johnson and Johnson Medical Devices, Irvine, CA 92618, USA'), 
                    #tags$h4(style="text-align:center;", tags$sup('c'), 
                    #        'Department of Biostatistics, Fielding School of Public Health, UCLA, Los Angeles, CA 90095, USA')
           )
  ),
  
  
  fluidRow(style='margin-right:8%;margin-left:8%;text-align: justify;font-size:xx-medium;color:#404040;',
           tags$br(),
           tags$h3('Abstract:'),
           tags$p('The work proposes a departure from the traditional experimental design to determine
                  a dose-response relationship in a developmental toxicology study. It is proposed 
                  that a model- based approach to determine a dose-response relationship can provide 
                  the most accurate statistical inference for the underlying parameters of interest,
                  which may be estimating one or more model parameters or pre-specified functions of 
                  the model parameters, such as lethal dose, at maximal efficiency. When the design 
                  criterion or criteria can be determined at the onset, there are demonstrated efficiency
                  gains by using a more carefully selected model-based optimal design as opposed to
                  an ad-hoc empirical design.  As an illustration, a model-based approach was theoretically
                  used to construct efficient designs for inference in a developmental toxicity study 
                  of sea urchin embryos exposed to trimethoprim.'),
           tags$p('Keywords: Approximate Design; D-optimality; Dose-Response; Optimal Experimental Design;
                  Sea Urchin Embryo, Trimethoprim.'),
           
           tags$h3('Dual objective optimal Designs'),
           tags$p('This app implements a dual objective design for developmental toxicology experiments.
                  Two objectives are D-optimality (for model parameters) and c-optimality (user-specified p% lethal dose).
                  An approximate design with \\(q\\) support points has the form 
						$$\\xi = \\left\\{\\begin{array}{cccc}
							\\begin{array}{c}x_1\\end{array} & \\begin{array}{c}x_2\\end{array} & \\cdots & 
							\\begin{array}{c}x_q\\end{array} \\\\
							w_1 & w_2 & \\cdots & w_q \\end{array}\\right\\},$$
						where \\((x_k)\\in[Lower bound,Upper bound]\\), \\(k = 1,\\ldots,q\\), are support points (dose levels)
						and \\(w_k\\) is the weight at the \\(k^{th}\\) support point
						satisfying \\(w_k\\in(0,1)\\) for all \\(k\\) and \\(\\sum_{k=1}^q w_k = 1\\).
						
                  The density of the response rate y under the Beta model is:
                  $$p(y)=\\frac{\\Gamma(a+b)}{\\Gamma(a)\\Gamma(b)}y^{a-1}(1-y)^{b-1}$$
                  where \\(y\\in[0,1], \\Gamma\\) is the Gamma function and
                  $$a=\\exp{(\\alpha_1+\\alpha_2x)}\\\\
                  b=\\exp{(\\beta_1+\\beta_2x)}$$
                  are two link functions depending on the dose level x. 
                  The parameters are \\(\\Theta=(\\alpha_1,\\alpha_2,\\beta_1,\\beta_2)\\). Hence, the mean
                  response rate at dose level x is:
                  $$f(x,\\theta)=\\frac{1}{1+\\exp{((\\beta_1-\\alpha_1)+(\\beta_2-\\alpha_2)x)}}$$'),
           tags$h4('D-optimality'),
           tags$p('D-optimality aims to maximize the determinant of the Fisher information matrix:
                  $$
						M(\\xi, \\theta) = \\sum_{k=1}^q w_k g(x_k,\\theta)g(x_k,\\theta)^\\top,\\,
						g(x_k,\\theta) = \\frac{\\partial\\log f(x_k,\\theta)}{\\partial\\theta},\\\\
						\\xi_D=\\arg\\max_{\\xi}\\log\\det M(\\xi, \\theta).
						$$'),
           tags$h4('c-optimality: user-specified p% lethal dose (LDp)'),
           tags$p('If interest in estimating the dose for which it will result in 
                  a user-specified percentage, say p, of the urchins experiencing 
                  fatality, i.e. the lethal dose LDp, one can find a design that 
                  minimizes the (asymptotic) of the variance of the estimate for LDp.  
                  This variance can be calculated based on the model.  Alternatively, 
                  a dual objective optimal design may be sought primarily for 
                  estimating a specific LDp, and secondly to estimate the model 
                  parameters as accurate as possible.'),
           
           tags$h4('Dual optimality'),
           tags$p('To search for the optimal design \\(\\xi\\), we first set the wegiht \\(W\\) to control the relative importance between two objectives,
                  then implement a PSO-type algorithm to optimize the following dual objective function:
                  $$\\xi_{dual}=\\arg\\max_{\\xi}W\\times \\text{D-optimality}+(1-W)\\times \\text{c-optimality} $$'),
           tags$p(' '),
           #tags$h3('PSO Algorithm'),
           #tags$p('The algorithm used here is from Hyun et al (2015), which is built upon the PSO algorithm. We give a brief introduction of the PSO algorithm in the following.'),
           #tags$p('Particle swarm optimization (PSO) is a powerful optimization tool which belongs to the family of metaheuristic algorithms.
						#PSO first initializes a flock of \\(P\\) particles, 
						#say \\(\\mathbf{x}^0_1, \\mathbf{x}^0_2, \\ldots, \\mathbf{x}^0_P\\), 
						#where each particle represents one candidate of the optimal design.  
						#At the \\(t^{th}\\) iteration, the particles update the following two formulae
						#$$
						#  \\mathbf{v}_j^{(t+1)} = \\omega^{(t)}\\mathbf{v}^{(t)}_j+c_1R_1\\bigotimes
						#  \\left(\\mathbf{x}^{(t)}_{j,L}-\\mathbf{x}^{(t)}_j\\right)+c_2R_2\\bigotimes\\left(\\mathbf{x}^{(t)}_G-\\mathbf{x}^{(t)}_j\\right),
						#$$
						#$$
						#  \\mathbf{x}_j^{t+1}=\\mathbf{x}_j^{(t)}+\\mathbf{v}_j^{(t+1)},\\,j=1,2,\\ldots,P.
						#$$
						#The operator \\(\\bigotimes\\) denotes the componentwise multiplication. 
						#The velocity of the \\(j^{th}\\) particle is denoted by \\(\\mathbf{v}_j^{(t+1)}\\) and it has three components:
						#its previous velocity \\(\\mathbf{v}_j^{(t)}\\) with which it flew to the current position \\(\\mathbf{x}^{(t)}_j\\). 
						#Let \\(\\mathbf{x}^{(t)}_{j,L}\\) be its local best position found so far and 
						#let \\(\\mathbf{x}^{(t)}_G\\) be the global best position the flock has found to date.
						#The two independent uniform random variates on \\((0,1)\\), \\(R_1\\) and \\(R_2\\), determine the 
						#momentum of particles toward to the local and global best positions.'
           #),
           #tags$p('The tuning parameters of PSO are: (i) \\(\\omega^{(t)}\\), the inertia weight, which is suggested to be a linearly decreasing sequence 
						#from \\(\\omega_0\\) to \\(\\omega_1\\) for the first \\(100\\times \\omega_v\\%\\) iterations and 
						#constantly affect \\(\\mathbf{v}^{(t)}_j\\) at the rate \\(\\omega_1\\) for the rest of iterations;
						#(ii) \\(c_1\\) and \\(c_2\\), which are the cognitive and the social parameters, respectively. They guide the particle
						#stochastic movement towards \\(\\mathbf{x}^t_{j,L}\\) and \\(\\mathbf{x}^t_G\\).  
						#Typically their default values are \\(c_1=c_2=2\\); 
						#(iii) velocity clamping, which is an user-defined threshold on the velocity for preventing an extremely large movement on the particles. 
						#When the absolute value of the velocity exceeeds the threshold, it will be adjusted to the limiting value.
						#This clamping is \\(1/V_K\\) of the range of the search space and the default value of \\(V_K=2\\).
						#'
           #),
  ),
  fluidRow(style="background-color:#87CEEB;", 
           tags$h2(style='margin-right:1%;margin-left:1%;',
                   tags$b('Implementation'))),
  tags$h4('Press the *search* button to run!'),
  tags$br(),
  # Application title
  #titlePanel("Dc Optimal Design for Developmental Toxicology Experiments"),
  
  # Sidebar with a slider input for number of bins 
  sidebarLayout(
    sidebarPanel(
      width = 4,
      numericInput(
        inputId = "LB", 
        label = h4(paste("Lower bound:")), 
        value = 0,
      ),
      helpText("LB: Predetermined lower bound of the dose range."),
      numericInput(
        inputId = "UB", 
        label = h4("Upper bound:"), 
        value = 1000,
      ),
      helpText("UB: Predetermined upper bound of the dose range."),
      numericInput(
        inputId = "LCp", 
        label = h4("LDp:"), 
        value = 0.5,
      ),
      helpText("LDp: User specified p% of lethal dose."),
      numericInput(
        inputId = "weight", 
        label = h4("Weight:"), 
        value = 0.5,
      ),
      helpText("Weight: weight to control the relative importance between two objectives: 1. estimating the model parameters; and 2. estimating the lethal dose LCp."),
      numericInput(
        inputId = "grid", 
        label = h4("Grid:"), 
        value = 1,
      ),
      helpText("Grid: The grid density to discretize the predetermined dose interval. Usually grid=1 is sufficient for plotting."),
      numericInput(
        inputId = "r", 
        label = h4("r:"), 
        value = 1,
      ),
      helpText("r: The number of iterations to select the initial design to search the optimal design. Usually r=1 is sufficient but r=0 also generates the optimal design."),
      tags$br(),
      
      matrixInput(
        inputId = "Lambda", class = "numeric",
        value = Lambda,
        label = h4("Lambda: "),
        rows = list(
          extend = FALSE,
          names = FALSE
        ),
        cols = list(
          names = TRUE
        )
      ),
      helpText("Lambda: The weight vector of different sets of nominal values below. Default is 1/6, i.e., equal weight for each set of 
               nominal values."),
      
      matrixInput(
        inputId =  "Parameters", class = "numeric",
        value = T,
        label = h4("Nominal values:"),
        rows = list(
          extend = FALSE
        ),
        cols = list(
          names = FALSE
        )
      ),
      helpText("The above matrix demonstrates 6 different sets of parameters to calculate the optimal design."),
      
      actionButton("search_button"," Search optimal design!",icon('search')),
    ),
    
    # Show a plot of the generated distribution
    mainPanel(
      tags$h3('Optimal Design'),
      plotOutput("plot") %>% withSpinner(type = 1, color = "darkorange"),
      textOutput("design"),
      tags$br(),
      tags$p('The above figure shows that when the response is studied using the given model
      with six sets of equally likely nominal values for the model parameters over 
      the user-specified design dose interval, the dual objective optimal design for estimating 
      the model parameters and the LDp has the selected doses with corresponding proportions 
      shown on the top left corner.  For example, if the total number of 
      subjects for the study is known and equal to N, we take roughly N times the 
      indicated proportions  of observations at the p% dose levels after rounding them up to integers and they sum to N.'),
      tags$p('The red dots indicate the doses of the generated design by an algorithm 
             and the plot in blue is called the sensitivity plot of the generated design. 
             If the plot is bounded above by unity throughout the dose interval and has 
             a peak value of one at the dose levels, then the generated design is optimal.  
             Otherwise it is not the best design and so does not have the most optimal 
             value among all designs on the given design interval.  Note that different 
             choices of values for Grid and r in the input boxes produce different designs
             and up to six different sets of possible values for the model parameters may 
             be specified.  If there is only one set of nominal values for the model
             parameters, we input the same values in each of the six rows.'),
      tags$h3('References'),
      tags$p('Hyun, SW., Wong, WK. (2015) Multiple objective optimal designs to study the interesting features in a dose response relationship. International Journal of Biostatistics. 11, 253-271.'),
      tags$p('RShiny official website: https://shiny.rstudio.com/articles/build.html, accessed on 09/14/2021.')
    )
  ),
)


cDopt = function(input, output) {
  
  output_plot <- eventReactive(input$search_button,{
    generate_plot(input$LB, input$UB, input$Parameters, input$LCp,
                  input$weight, input$grid, input$r, input$Lambda)
  })
  
  output$plot = renderPlot({output_plot()})
}

# Run the application 
shinyApp(ui = ui, server = cDopt)
