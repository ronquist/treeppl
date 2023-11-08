library(castor)

rate_matrix <- function(lambda)
{
    data <- c(-lambda[1],              lambda[1],        0.0,
               lambda[2], -(lambda[2]+lambda[3]),  lambda[3],
                     0.0,              lambda[4], -lambda[4])

    matrix (byrow=TRUE, nrow=3, ncol=3, data=data)
}

