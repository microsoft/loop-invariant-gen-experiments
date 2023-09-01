/*
Commit Number: 084a7f4a5a5c859ab24e727ef92f9b2ed8611acf
URL: https://github.com/tieto/pidgin/commit/084a7f4a5a5c859ab24e727ef92f9b2ed8611acf
Project Name: pidgin
License: GPL-2.0
termination: FALSE
*/
#include <stdlib.h>
typedef struct gaim_xfer{
	int watcher;
	int fd;
	int bytes_remaining;
}gaim_xfer;
void gaim_xfer_destroy(struct gaim_xfer *xfer);

void gaim_xfer_cancel(struct gaim_xfer *xfer)
{
	if (xfer == 0)
		return;
	if (xfer->watcher != 0) {
		xfer->watcher = 0;
	}
	if (xfer->fd != 0)
		xfer->fd = 0;
	/* Delete the transfer. */
	gaim_xfer_destroy(xfer);
}

void gaim_xfer_destroy(struct gaim_xfer *xfer)
{

	if (xfer == 0)
		return;

	if (xfer->bytes_remaining > 0) {
		gaim_xfer_cancel(xfer);
		return;
	}
	free(xfer);
}

int main()
{
	struct gaim_xfer a1;
	struct gaim_xfer* a = &a1;
	a->bytes_remaining =  __VERIFIER_nondet_int();
	a->fd = __VERIFIER_nondet_int();
	a->watcher = __VERIFIER_nondet_int();
	gaim_xfer_cancel(a);
	return 0;
}
