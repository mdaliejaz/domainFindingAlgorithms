#include <R.h>
#include <time.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <string.h>
#include <math.h>
#include <gsl/gsl_matrix.h>
#include <gsl/gsl_sf_gamma.h>

int Function_HiC_R(int *size, int *maximum_no_change_points,
	char **distribution, double *matrix, int *out_t_hat,
	double *out_log_likelihood, int *out_est_chng_pt, char **model_type)
{
	/*
	 * R sends pointers of each data, keeping it that way for now.
	 * This section can be removed if parameters received by
	 * this method is changed.
	 */
	int size_matrix = *size;
	int max_chng_pts = *maximum_no_change_points;
	char *distrib = *distribution;
	char *model = *model_type;
	/*
	 * End sanitizing input data
	 */

	int i, j, k, l, size_mat_extr, i_coin, j_coin, size_coin, n_coin, size_mu;
	int ind_max, u;
	double sum, sum_hat, loglambdahat, sum_carr;
	double max, mu_hat, var_hat, phi_hat, lambda_hat, mu;
	double vecteur[size_matrix - 1];
	double t_est[max_chng_pts][max_chng_pts], y[size_matrix][size_matrix];
	double Delta[size_matrix][size_matrix], Exterieur[size_matrix][size_matrix];
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
			// Copying input data matrix to matrix Y
			y[i][j] = matrix[i * size_matrix + j];
			// 1E100 = scientific notation for vary large number.
			// -1E100 = (-) 1 followed by 100 zeroes
			Delta[i][j] = -1E100;
			Exterieur[i][j] = -1E100;
			T[i][j] = -1E100;
			D[i][j] = -1E100;
			R[i][j] = -1E100;
			Tcarr[i][j] = -1E100;
			Dcarr[i][j] = -1E100;
			Rcarr[i][j] = -1E100;
		}
	}


	/*
	 * The following code is common for all the three distributions
	 * The first row and the diagonal of matrix T and D are populated
	 */
	// Calculating amounts in trapezes
	T[0][0] = y[0][0];
	D[0][0] = y[0][0];
	for (k = 1; k < size_matrix; k++) {
		T[0][k] = T[0][(k - 1)] + y[0][k];
		D[k][k] = y[k][k];
		sum = 0;
		for (i = 0; i <= k; i++) {
			sum = sum + y[i][k];
		}
		T[k][k] = T[(k - 1)][(k - 1)] + sum;
		D[0][k] = T[k][k];
	}

	/*
	 * Calulating the rest of the elements of matrices T and D.
	 * Used in both D and Dplus.
	 */
	for (i = 1; i < (size_matrix - 1); i++) {
		for (j = (i + 1); j < size_matrix; j++) {
			sum = 0;
			for (k = 0; k <= i; k++) 
				sum = sum + y[k][j];
			T[i][j] = T[i][(j - 1)] + sum;
			R[i][j] = T[(i - 1)][j] - T[(i - 1)][(i - 1)];
			D[i][j] = T[j][j] - T[(i - 1)][j];
		}
	}

	/* The common code (except Dplus of Poisson distribution 
	 * that is used to calculate hat for each distribution. 
	 */
	n_coin = (int)floor(size_matrix / 4);
	size_coin = (n_coin + 1) * n_coin / 2;
	j_coin = 3 * n_coin;
	i_coin = n_coin;
	sum_hat = 0;

	for (i = 0; i < i_coin; i++) {
		for (j = j_coin; j < size_matrix; j++) {
			if ((j - j_coin) >= i) {
				sum_hat = sum_hat + y[i][j];
			}
		}
	}


	// Poisson Distribution
	if (strcmp(distrib, "P") == 0) {
		// Calculating amounts in trapezes
		if (D[0][0] != 0)
			Delta[0][0] = D[0][0] * (log(D[0][0]) - 1);
		for (k = 1; k < size_matrix; k++)
		{
			if (D[0][k] != 0)
				Delta[0][k] = D[0][k] * (log(D[0][k]) - log((pow(k, 2) + k) / 2) - 1);
			if (D[k][k] != 0)
				Delta[k][k] = D[k][k] * (log(D[k][k]) - 1);
		}

		if (strcmp(model, "Dplus") == 0) {
			for (i = 1; i < (size_matrix - 1); i++) {
				for (j = (i + 1); j < size_matrix; j++) {
					size_mat_extr = (j - i + 1) * (j - i) / 2 + (j - i + 1);
					if ((D[i][j] != 0) && (size_mat_extr != 0)) {
						Delta[i][j] = D[i][j] * (log(D[i][j]) - log(size_mat_extr) - 1);
					}
					size_mat_extr = i * (j - i + 1);
					if ((R[i][j] != 0) && (size_mat_extr != 0)) {
						Exterieur[i][j] = R[i][j] * (log(R[i][j]) - log(size_mat_extr) - 1);
					}
				}
			}
		}
		else if (strcmp(model, "D") == 0) {
			// Calculating lambda_hat
			lambda_hat = sum / size_coin;
			loglambdahat = log(lambda_hat);

			for (i = 1; i < (size_matrix - 1); i++) {
				for (j = (i + 1); j < size_matrix; j++) {
					size_mat_extr = (j - i + 1) * (j - i) / 2 + (j - i + 1);
					if ((D[i][j] != 0) && (size_mat_extr != 0)) {
						Delta[i][j] = D[i][j] * (log(D[i][j]) - log(size_mat_extr) - 1);
					}
					size_mat_extr = i * (j - i + 1);
					Exterieur[i][j] = R[i][j] * loglambdahat - size_mat_extr * lambda_hat;
				}
			}
		}
	} else if (strcmp(distrib, "B") == 0) {

		///// Calculating phi_hat and mu_hat
		sum_carr = 0;

		for (i = 0; i < i_coin; i++) {
			for (j = (j_coin - 1); j < size_matrix; j++) {
				if ((j - j_coin) >= i) {
					sum_carr = sum_carr + pow(y[i][j], 2);
				}
			}
		}
		mu_hat = sum_hat / size_coin;
		var_hat = sum_carr / (size_coin - 1) - size_coin * pow(mu_hat, 2) / (size_coin - 1);
		phi_hat = pow(mu_hat, 2) / (var_hat - mu_hat);

		/////  Calculating amounts in trapezes
		if (((phi_hat + D[0][0]) > 0) && (D[0][0] > 0))
			Delta[0][0] = -(phi_hat + D[0][0]) * log(phi_hat + D[0][0]) + D[0][0] * log(D[0][0]);
		for (k = 1; k < size_matrix; k++) {
			size_mu = ((pow(k + 1, 2) + k + 1) / 2);
			mu = D[0][k] / size_mu;
			if (D[0][k] > 0)
				Delta[0][k] = -(size_mu * phi_hat + D[0][k]) * log(phi_hat + mu) + D[0][k] * log(mu);
			if (D[k][k] > 0)
				Delta[k][k] = -(phi_hat + D[k][k]) * log(phi_hat + D[k][k]) + D[k][k] * log(D[k][k]);
		}

		if (strcmp(model, "Dplus") == 0) {
			for (i = 1; i < (size_matrix - 1); i++) {
				for (j = (i + 1); j < size_matrix; j++) {
					size_mat_extr = (j - i + 1) * (j - i) / 2 + (j - i + 1);
					if ((D[i][j] > 0) && (size_mat_extr != 0)) {
						mu = D[i][j] / size_mat_extr;
						Delta[i][j] = -(size_mat_extr * phi_hat + D[i][j]) * log(phi_hat + mu) + D[i][j] * log(mu);
					}
					size_mat_extr = i * (j - i + 1);
					if ((R[i][j] > 0) && (size_mat_extr != 0)) {
						mu = R[i][j] / size_mat_extr;
						Exterieur[i][j] = -(size_mat_extr * phi_hat + R[i][j]) * log(phi_hat + mu) + R[i][j] * log(mu);
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
						Delta[i][j] = -(size_mat_extr * phi_hat + D[i][j]) * log(phi_hat + mu) + D[i][j] * log(mu);
					}
					size_mat_extr = i * (j - i + 1);
					if (((phi_hat + mu_hat) > 0) && (mu_hat != 0)) {
						Exterieur[i][j] = -(size_mat_extr * phi_hat + R[i][j]) * log(phi_hat + mu_hat) + R[i][j] * log(mu_hat);
					}
				}
			}
		}
	} else if (strcmp(distrib, "G") == 0) {

		mu_hat = sum_hat / size_coin;

		//  Calculating amounts in trapezes
		Tcarr[0][0] = pow(y[0][0], 2);
		Dcarr[0][0] = pow(y[0][0], 2);
		Delta[0][0] = 0;

		for (k = 1; k < size_matrix; k++) {
			Tcarr[0][k] = Tcarr[0][(k - 1)] + pow(y[0][k], 2);
			Dcarr[k][k] = pow(y[k][k], 2);
			sum_carr = 0;
			for (i = 0; i <= k; i++) {
				sum_carr = sum_carr + pow(y[i][k], 2);
			}
			Tcarr[k][k] = Tcarr[(k - 1)][(k - 1)] + sum_carr;
			Dcarr[0][k] = Tcarr[k][k];
			mu = D[0][k] / ((pow(k + 1, 2) + k + 1) / 2);
			Delta[0][k] = -(Dcarr[0][k] - D[0][k] * mu);
			Delta[k][k] = 0;
		}

		if (strcmp(model, "Dplus") == 0) {
			for (i = 1; i < (size_matrix - 1); i++) {
				for (j = (i + 1); j < size_matrix; j++) {
					sum_carr = 0;
					for (k = 0; k <= i; k++) {
						sum_carr = sum_carr + pow(y[k][j], 2);
					}
					Tcarr[i][j] = Tcarr[i][(j - 1)] + sum_carr;
					Rcarr[i][j] = Tcarr[(i - 1)][j] - Tcarr[(i - 1)][(i - 1)];
					Dcarr[i][j] = Tcarr[j][j] - Tcarr[(i - 1)][j];

					size_mat_extr = (j - i + 1) * (j - i) / 2 + (j - i + 1);
					mu = D[i][j] / size_mat_extr;
					Delta[i][j] = -(Dcarr[i][j] - D[i][j] * mu);

					size_mat_extr = i * (j - i + 1);
					mu = R[i][j] / size_mat_extr;
					Exterieur[i][j] = -(Rcarr[i][j] - pow(mu, 2) * size_mat_extr);
				}
			}
		}
		else if (strcmp(model, "D") == 0) {
			for (i = 1; i < (size_matrix - 1); i++) {
				for (j = (i + 1); j < size_matrix; j++) {
					sum_carr = 0;
					for (k = 0; k <= i; k++) {
						sum_carr = sum_carr + pow(y[k][j], 2);
					}
					Tcarr[i][j] = Tcarr[i][(j - 1)] + sum_carr;
					Rcarr[i][j] = Tcarr[(i - 1)][j] - Tcarr[(i - 1)][(i - 1)];
					Dcarr[i][j] = Tcarr[j][j] - Tcarr[(i - 1)][j];

					size_mat_extr = (j - i + 1) * (j - i) / 2 + (j - i + 1);
					mu = D[i][j] / size_mat_extr;
					Delta[i][j] = -(Dcarr[i][j] - D[i][j] * mu);

					size_mat_extr = i * (j - i + 1);
					Exterieur[i][j] = -(Rcarr[i][j] - pow(mu_hat, 2) * size_mat_extr);
				}
			}
		}
	} else
		return EXIT_FAILURE;

	/////// dynamic programming ///////////

	for (i = 0; i <= max_chng_pts - 1; i++) {
		for (j = 0; j < size_matrix; j++) {
			if(i < max_chng_pts-1)
				t_matrix[i][j] = -1;
			if(i!=0)
				I[i][j] = -1E100;
			else
				I[i][j] = Delta[0][j];
		}
	}

	for (k = 1; k <= max_chng_pts - 1; k++) {
		for (l = k; l < size_matrix; l++) {
			for (i = 0; i < size_matrix - 1; i++) {
				vecteur[i] = -1E100;
			}
			for (u = 1; u <= l; u++) {
				vecteur[u - 1] = I[k - 1][u - 1] + Delta[u][l] + Exterieur[u][l];
			}
			ind_max = 0;
			max = vecteur[0];
			for (u = 0; u < size_matrix - 1; u++) {
				if (vecteur[u] > max) {
					max = vecteur[u];
					ind_max = u;
				}
			}
			I[k][l] = max;
			t_matrix[k - 1][l] = ind_max;
		}
	}

	ind_max=0;
	max=I[0][size_matrix-1];
	for (i=0;i<max_chng_pts;i++) {
		out_log_likelihood[i] = I[i][size_matrix-1];
		if((I[i][size_matrix-1])>max) {
			max=I[i][size_matrix-1];
			ind_max=i;
		}
	}

	for (i = 0; i < max_chng_pts; i++) {
		for (j = 0; j < max_chng_pts; j++) {
			if(i != j)
				t_est[i][j] = -1;
			else
				t_est[i][j] = size_matrix - 1;
		}
	}

	/////// Calculating change-point /////////
	for (j = 1; j < max_chng_pts; j++) {
		for (k = j - 1; k >= 0; k--) {
			t_est[j][k] = t_matrix[k][(int)t_est[j][k + 1]];
		}
	}

	//////// Calculating max index /////////

	for (i = 0; i < max_chng_pts; i++) {
		out_t_hat[i] = (int) t_est[ind_max][i] + 1;
		for (j = 0; j < max_chng_pts; j++) {
			out_est_chng_pt[i * max_chng_pts + j] = (int) t_est[i][j] + 1;
		}
	}
	return (EXIT_SUCCESS);
}
