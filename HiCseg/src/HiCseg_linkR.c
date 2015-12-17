#include <R.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

/*
 * This function is called from the R module with the following parameters
 * size - size of the input matrix
 * maximum_no_change_points - Maximum number of change points that needs to
 *							  be calculated.
 * distribution - The distribution to be used:
 *				  a) Poisson (P)
 *				  b) Gaussian (G)
 *				  c) Negative Binomial (B)
 * matrix - The input matrix
 * out_t_hat - Pointer returned back to R with the estimated change points
 * out_log_likelihood - Pointer returned back to R with log-likelihood for
 *						different number of change-points
 * out_est_chng_pt - Pointer returned back to R with matrix of the
 *					 estimated change-points for different possible number
 *					 of change-points
 * model_type - D or Dplus (block digonal or extended block diagonal)
 */
int Function_HiC_R(int *size, int *maximum_no_change_points,
                   char **distribution, double *matrix, int *out_t_hat,
                   double *out_log_likelihood, int *out_est_chng_pt,
                   char **model_type)
{
	/*
	 * R sends pointers of each data to this matrix.
	 * Getting the data from these pointers.
	 * Note:
	 * This section can be removed if parameters received by the method is
	 * changed, that is, if the method is interfaced with any other
	 * statistical computing Language other than R
	 */
	int size_matrix = *size;
	int max_chng_pts = *maximum_no_change_points;
	char *distrib = *distribution;
	char *model = *model_type;
	/*
	 * End sanitizing input data
	 */

	int i, j, k, l, x, size_mat_extr, i_corner, j_corner, size_corner, n_corner;
	int ind_max, u, size_mu;
	double sum, sum_hat, loglambdahat, sum_carr;
	double max, mu_hat, var_hat, phi_hat, lambda_hat, mu;
	double max_vector[size_matrix - 1];
	double t_est[max_chng_pts][max_chng_pts], Y[size_matrix][size_matrix];
	double delta[size_matrix][size_matrix], exterior[size_matrix][size_matrix];
	double T[size_matrix][size_matrix], D[size_matrix][size_matrix];
	double R[size_matrix][size_matrix], Tcarr[size_matrix][size_matrix];
	double Dcarr[size_matrix][size_matrix], Rcarr[size_matrix][size_matrix];
	double I[max_chng_pts][size_matrix], t_matrix[max_chng_pts - 1][size_matrix];


	// Early exit for wrong parameters
	if ((strcmp(model, "D") != 0) && (strcmp(model, "Dplus") != 0))
		return EXIT_FAILURE;

	if ((strcmp(distrib, "P") != 0) && (strcmp(distrib, "B") != 0) &&
	        (strcmp(distrib, "G") != 0))
		return EXIT_FAILURE;

	// initialize all the matrices
	for (i = 0; i < size_matrix; i++) {
		for (j = 0; j < size_matrix; j++) {
			// Copying input data matrix (received as a pointer) to matrix Y
			Y[i][j] = matrix[i * size_matrix + j];
			// 1E100 = scientific notation for vary large number.
			// -1E100 = (-) 1 followed by 100 zeroes
			delta[i][j] = -1E100;
			exterior[i][j] = -1E100;
			T[i][j] = -1E100;
			D[i][j] = -1E100;
			R[i][j] = -1E100;
			Tcarr[i][j] = -1E100;
			Dcarr[i][j] = -1E100;
			Rcarr[i][j] = -1E100;
		}
	}


	/*
	 * The following code is common for all the three distributions.
	 * T is a temporary matrix in which each cell contains the mean of
	 * the values above and before it. It is used to calculate the mean
	 * of the domain region (in matrix D) and the non domain region (in
	 * matrix R).
	 * The first row and the diagonal of matrix T and D are populated here.
	 * Each element in the first row of T matrix contains the sum
	 * of all the elements of Y matrix in the first row upto that position.
	 * Eg.: T[0][4] = Y[0][0] + Y[0][1] + Y[0][2] + Y[0][3] + Y[0][4].
	 * Each element in the diagonal of T matrix contains the sum of elements
	 * of Y matrix that make up the upper traingle in Y.
	 * Eg.: T[2][2] = Y[0][0] + Y[0][1] + Y[0][2] + Y[1][1] + Y[1][2] + Y[2][2]
	 * First row of D matrix copies the diagonal matrix of T.
	 * Diagonal of D matrix copies the diagonal matrix of Y.
	 */
	T[0][0] = Y[0][0];
	D[0][0] = Y[0][0];
	for (k = 1; k < size_matrix; k++) {
		T[0][k] = T[0][(k - 1)] + Y[0][k];
		D[k][k] = Y[k][k];
		sum = 0;
		for (i = 0; i <= k; i++) {
			sum = sum + Y[i][k];
		}
		T[k][k] = T[(k - 1)][(k - 1)] + sum;
		D[0][k] = T[k][k];
	}

	/*
	 * Calulating the rest of the elements of matrices T and D.
	 * The other elements in the T and D matrices are the elements apart
	 * from the first row and the diagonal. Any such element in T matrix
	 * is the sum of all the elements of Y matrix that is above it and
	 * before it, including the element at the same position.
	 * Eg.: T[1][2] = Y[0][0] + Y[0][1] + Y[1][1] + Y[0][2] + Y[1][2]
	 * Any such element in D represents the values in the domain region.
	 * For eg.: D[5][6] = T[6][6] - T[4][6]
	 * Any such element in R represents the values in the non domain region.
	 * For eg.: R[3][4] = T[2][4] - T[2][2]
	 * Used in both D and Dplus of every distribution.
	 */
	for (i = 1; i < (size_matrix - 1); i++) {
		for (j = (i + 1); j < size_matrix; j++) {
			sum = 0;
			for (k = 0; k <= i; k++)
				sum = sum + Y[k][j];
			T[i][j] = T[i][(j - 1)] + sum;
			R[i][j] = T[(i - 1)][j] - T[(i - 1)][(i - 1)];
			D[i][j] = T[j][j] - T[(i - 1)][j];
		}
	}

	/*
	 * The common code (except Dplus of Poisson distribution)
	 * that is used to calculate hat for each distribution.
	 */
	n_corner = (int)floor(size_matrix / 4);
	size_corner = (n_corner + 1) * n_corner / 2;
	j_corner = 3 * n_corner;
	i_corner = n_corner;
	sum_hat = 0;

	/*
	 * To calculate the sum of non domain regions in the
	 * D model (of Poisson and Gaussian), find the sum of Y[i][j],
	 * where 0 <= i < (size/4) and 3(size/4) <= j < size,
	 * that is find the mean from top right corner, and use it for
	 * all the calculations since the mean is considered constant in D model.
	 *
	 * Note:
	 * For Binomial distributon the iteration for the inner loop begins
	 * from j_corner - 1 in the old French version of this code.
	 * But this is probably a bug and as such we are not doing that. It being
	 * a bug can be confirmed from Fig 2 in the referenced paper:
	 * Two-dimensional segmentation for analyzing Hi-C data.
	 * However, for consistency, we are not changing the behavior.
	 * The if condition needs to be removed in the following to make the
	 * behavior correct.
	 */
	if (strcmp(distrib, "B") == 0) {
		x = j_corner - 1;
	} else {
		x = j_corner;
	}

	/* Calculation of sum_hat */
	for (i = 0; i < i_corner; i++) {
		for (j = x; j < size_matrix; j++) {
			if ((j - j_corner) >= i) {
				sum_hat = sum_hat + Y[i][j];
			}
		}
	}

	/* Poisson Distribution */
	if (strcmp(distrib, "P") == 0) {
		/* Populating the delta matrix */
		if (D[0][0] != 0)
			delta[0][0] = D[0][0] * (log(D[0][0]) - 1);
		for (k = 1; k < size_matrix; k++)
		{
			if (D[0][k] != 0)
				delta[0][k] = D[0][k] * (log(D[0][k]) - log((pow(k, 2) + k) / 2) - 1);
			if (D[k][k] != 0)
				delta[k][k] = D[k][k] * (log(D[k][k]) - 1);
		}

		if (strcmp(model, "Dplus") == 0) {
			for (i = 1; i < (size_matrix - 1); i++) {
				for (j = (i + 1); j < size_matrix; j++) {
					size_mat_extr = (j - i + 1) * (j - i) / 2 + (j - i + 1);
					if ((D[i][j] != 0) && (size_mat_extr != 0)) {
						delta[i][j] = D[i][j] * (log(D[i][j]) - log(size_mat_extr) - 1);
					}
					size_mat_extr = i * (j - i + 1);
					if ((R[i][j] != 0) && (size_mat_extr != 0)) {
						exterior[i][j] = R[i][j] * (log(R[i][j]) - log(size_mat_extr) - 1);
					}
				}
			}
		}
		else if (strcmp(model, "D") == 0) {
			/* Calculating lambda_hat */
			lambda_hat = sum_hat / size_corner;
			loglambdahat = log(lambda_hat);

			/* Populating the delta matrix */
			for (i = 1; i < (size_matrix - 1); i++) {
				for (j = (i + 1); j < size_matrix; j++) {
					size_mat_extr = (j - i + 1) * (j - i) / 2 + (j - i + 1);
					if ((D[i][j] != 0) && (size_mat_extr != 0)) {
						delta[i][j] = D[i][j] * (log(D[i][j]) - log(size_mat_extr) - 1);
					}
					size_mat_extr = i * (j - i + 1);
					exterior[i][j] = R[i][j] * loglambdahat - size_mat_extr * lambda_hat;
				}
			}
		}
	} else if (strcmp(distrib, "B") == 0) {
		/* Calculating phi_hat and mu_hat */
		sum_carr = 0;
		for (i = 0; i < i_corner; i++) {
			for (j = (j_corner - 1); j < size_matrix; j++) {
				if ((j - j_corner) >= i) {
					sum_carr = sum_carr + pow(Y[i][j], 2);
				}
			}
		}
		mu_hat = sum_hat / size_corner;
		var_hat = sum_carr / (size_corner - 1) - size_corner * pow(mu_hat, 2) /
		          (size_corner - 1);
		phi_hat = pow(mu_hat, 2) / (var_hat - mu_hat);

		/* Populating the delta matrix */
		if (((phi_hat + D[0][0]) > 0) && (D[0][0] > 0))
			delta[0][0] = -(phi_hat + D[0][0]) * log(phi_hat +
			              D[0][0]) + D[0][0] * log(D[0][0]);
		for (k = 1; k < size_matrix; k++) {
			size_mu = ((pow(k + 1, 2) + k + 1) / 2);
			mu = D[0][k] / size_mu;
			if (D[0][k] > 0)
				delta[0][k] = -(size_mu * phi_hat + D[0][k]) *
				              log(phi_hat + mu) + D[0][k] * log(mu);
			if (D[k][k] > 0)
				delta[k][k] = -(phi_hat + D[k][k]) * log(phi_hat + D[k][k]) +
				              D[k][k] * log(D[k][k]);
		}

		if (strcmp(model, "Dplus") == 0) {
			for (i = 1; i < (size_matrix - 1); i++) {
				for (j = (i + 1); j < size_matrix; j++) {
					size_mat_extr = (j - i + 1) * (j - i) / 2 + (j - i + 1);
					if ((D[i][j] > 0) && (size_mat_extr != 0)) {
						mu = D[i][j] / size_mat_extr;
						delta[i][j] = -(size_mat_extr * phi_hat + D[i][j]) *
						              log(phi_hat + mu) + D[i][j] * log(mu);
					}
					size_mat_extr = i * (j - i + 1);
					if ((R[i][j] > 0) && (size_mat_extr != 0)) {
						mu = R[i][j] / size_mat_extr;
						exterior[i][j] = -(size_mat_extr * phi_hat + R[i][j]) *
						                 log(phi_hat + mu) + R[i][j] * log(mu);
					}
				}
			}
		}
		else if (strcmp(model, "D") == 0) {
			for (i = 1; i < (size_matrix - 1); i++) {
				for (j = (i + 1); j < size_matrix; j++) {
					size_mat_extr = (j - i + 1) * (j - i) / 2 + (j - i + 1);
					if ((D[i][j] > 0) && (size_mat_extr != 0)) {
						mu = D[i][j] / size_mat_extr;
						delta[i][j] = -(size_mat_extr * phi_hat + D[i][j]) *
						              log(phi_hat + mu) + D[i][j] * log(mu);
					}
					size_mat_extr = i * (j - i + 1);
					if (((phi_hat + mu_hat) > 0) && (mu_hat != 0)) {
						exterior[i][j] = -(size_mat_extr * phi_hat + R[i][j]) *
						                 log(phi_hat + mu_hat) + R[i][j] * log(mu_hat);
					}
				}
			}
		}
	} else if (strcmp(distrib, "G") == 0) {
		mu_hat = sum_hat / size_corner;
		Tcarr[0][0] = pow(Y[0][0], 2);
		Dcarr[0][0] = pow(Y[0][0], 2);
		delta[0][0] = 0;
		/* Populating the delta matrix */
		for (k = 1; k < size_matrix; k++) {
			Tcarr[0][k] = Tcarr[0][(k - 1)] + pow(Y[0][k], 2);
			Dcarr[k][k] = pow(Y[k][k], 2);
			sum_carr = 0;
			for (i = 0; i <= k; i++) {
				sum_carr = sum_carr + pow(Y[i][k], 2);
			}
			Tcarr[k][k] = Tcarr[(k - 1)][(k - 1)] + sum_carr;
			Dcarr[0][k] = Tcarr[k][k];
			mu = D[0][k] / ((pow(k + 1, 2) + k + 1) / 2);
			delta[0][k] = -(Dcarr[0][k] - D[0][k] * mu);
			delta[k][k] = 0;
		}
		if (strcmp(model, "Dplus") == 0) {
			for (i = 1; i < (size_matrix - 1); i++) {
				for (j = (i + 1); j < size_matrix; j++) {
					sum_carr = 0;
					for (k = 0; k <= i; k++) {
						sum_carr = sum_carr + pow(Y[k][j], 2);
					}
					Tcarr[i][j] = Tcarr[i][(j - 1)] + sum_carr;
					Rcarr[i][j] = Tcarr[(i - 1)][j] - Tcarr[(i - 1)][(i - 1)];
					Dcarr[i][j] = Tcarr[j][j] - Tcarr[(i - 1)][j];
					size_mat_extr = (j - i + 1) * (j - i) / 2 + (j - i + 1);
					mu = D[i][j] / size_mat_extr;
					delta[i][j] = -(Dcarr[i][j] - D[i][j] * mu);
					size_mat_extr = i * (j - i + 1);
					mu = R[i][j] / size_mat_extr;
					exterior[i][j] = -(Rcarr[i][j] - pow(mu, 2) * size_mat_extr);
				}
			}
		}
		else if (strcmp(model, "D") == 0) {
			for (i = 1; i < (size_matrix - 1); i++) {
				for (j = (i + 1); j < size_matrix; j++) {
					sum_carr = 0;
					for (k = 0; k <= i; k++) {
						sum_carr = sum_carr + pow(Y[k][j], 2);
					}
					Tcarr[i][j] = Tcarr[i][(j - 1)] + sum_carr;
					Rcarr[i][j] = Tcarr[(i - 1)][j] - Tcarr[(i - 1)][(i - 1)];
					Dcarr[i][j] = Tcarr[j][j] - Tcarr[(i - 1)][j];
					size_mat_extr = (j - i + 1) * (j - i) / 2 + (j - i + 1);
					mu = D[i][j] / size_mat_extr;
					delta[i][j] = -(Dcarr[i][j] - D[i][j] * mu);
					size_mat_extr = i * (j - i + 1);
					exterior[i][j] = -(Rcarr[i][j] - pow(mu_hat, 2) * size_mat_extr);
				}
			}
		}
	}

	/*dynamic programming */

	/*
	 * Computation of the elements of matrix 'I' - used to compute the maximum
	 *										over the sum of delta and exterior.
	 * The value of the elements of the first row of matrix 'I' is initialized
	 * with the elements of the first row of Delta matrix,
	 * The remaining elements of the matrix 'I' are initialized to -1E100.
	 */
	for (i = 0; i <= max_chng_pts - 1; i++) {
		for (j = 0; j < size_matrix; j++) {
			if (i < max_chng_pts - 1)
				t_matrix[i][j] = -1;
			if (i != 0)
				I[i][j] = -1E100;
			else
				I[i][j] = delta[0][j];
		}
	}

	/*
	 * Using temporary max_vector matrix to find max for matrix 'I'.
	 * The values in max_vector is computed using matrices I, delta and
	 * exterior followed by finding the max among all the max_vector values
	 * which is stored in matrix I and the corresponding index in a
	 * matrix called t_matrix which will be used to generate the estimated
	 * change points.
	 */
	for (k = 1; k <= max_chng_pts - 1; k++) {
		for (l = k; l < size_matrix; l++) {
			for (i = 0; i < size_matrix - 1; i++) {
				max_vector[i] = -1E100;
			}
			for (u = 1; u <= l; u++) {
				max_vector[u - 1] = I[k - 1][u - 1] + delta[u][l] + exterior[u][l];
			}
			ind_max = 0;
			max = max_vector[0];
			for (u = 0; u < size_matrix - 1; u++) {
				if (max_vector[u] > max) {
					max = max_vector[u];
					ind_max = u;
				}
			}
			I[k][l] = max;
			t_matrix[k - 1][l] = ind_max;
		}
	}

	/*
	 * After the calculation of the value of the elements of the 'I' matrix,
	 * the last column of the elements of the 'I' matrix is stored in the
	 * 'out_log_likelihood' matrix. Also the index of the maximum element is
	 * stored in ind_max to later find the index for max log likelihood for
	 * different change points
	 */
	ind_max = 0;
	max = I[0][size_matrix - 1];
	for (i = 0; i < max_chng_pts; i++) {
		out_log_likelihood[i] = I[i][size_matrix - 1];
		if ((I[i][size_matrix - 1]) > max) {
			max = I[i][size_matrix - 1];
			ind_max = i;
		}
	}

	/*
	 * Initializing estmimation matrix
	 * (will be copied over to returning pointer)
	 */
	for (i = 0; i < max_chng_pts; i++) {
		for (j = 0; j < max_chng_pts; j++) {
			if (i != j)
				t_est[i][j] = -1;
			else
				t_est[i][j] = size_matrix - 1;
		}
	}

	/*
	 * Calculation of change-point
	 */
	for (j = 1; j < max_chng_pts; j++) {
		for (k = j - 1; k >= 0; k--) {
			t_est[j][k] = t_matrix[k][(int)t_est[j][k + 1]];
		}
	}

	/*
	 * Copying data to the returning pointers.
	 * The values of the elements of the matrix 'out_t_hat' contains the
	 * change-points where the log likelihood is maximized.
	 * The values of the elements of the matrix 'out_est_chng_pt' contains
	 * the estimation of the max change points for different possible number of
	 * change points.
	 */
	for (i = 0; i < max_chng_pts; i++) {
		out_t_hat[i] = (int) t_est[ind_max][i] + 1;
		for (j = 0; j < max_chng_pts; j++) {
			out_est_chng_pt[i * max_chng_pts + j] = (int) t_est[i][j] + 1;
		}
	}
	return (EXIT_SUCCESS);
}
